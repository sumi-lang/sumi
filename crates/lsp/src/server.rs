use std::collections::HashMap;
use std::thread;

use crossbeam_channel::{Receiver, Sender, select, unbounded};
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::Notification as _;
use lsp_types::request::Request as _;
use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOptions, CodeActionOrCommand, CodeActionParams,
    CodeActionProviderCapability, DiagnosticRelatedInformation, DiagnosticSeverity,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DocumentFormattingParams, DocumentSymbol, DocumentSymbolParams, DocumentSymbolResponse,
    InitializeParams, InitializeResult, Location, OneOf, OptionalVersionedTextDocumentIdentifier,
    PositionEncodingKind, PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo,
    SymbolInformation, SymbolKind, TextDocumentEdit, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, TextEdit, Uri, WorkspaceEdit,
};
use serde_json::Value;
use sumi_frontend::{Diagnostic, Fix, parse_source};
use sumi_hir::analyze;

use crate::position::{Encoding, Positions};

#[derive(Clone)]
struct Document {
    generation: u64,
    version: i32,
    text: String,
}

struct Snapshot {
    generation: u64,
    version: i32,
    fixes: Vec<LspFix>,
}

#[derive(Clone, Copy)]
struct ClientFeatures {
    code_actions: bool,
    hierarchical_symbols: bool,
    preferred_actions: bool,
    related_information: bool,
}

struct LspFix {
    diagnostic: lsp_types::Diagnostic,
    title: String,
    edit: TextEdit,
}

enum Job {
    Analyze {
        uri: Uri,
        generation: u64,
        version: i32,
        text: String,
    },
    Format {
        id: RequestId,
        uri: Uri,
        generation: u64,
        version: i32,
        text: String,
    },
    Symbols {
        id: RequestId,
        uri: Uri,
        generation: u64,
        version: i32,
        text: String,
    },
}

enum Outcome {
    Analyzed {
        uri: Uri,
        generation: u64,
        version: i32,
        diagnostics: Vec<lsp_types::Diagnostic>,
        fixes: Vec<LspFix>,
    },
    Response {
        id: RequestId,
        uri: Uri,
        generation: u64,
        version: i32,
        result: Value,
    },
}

pub fn run_stdio() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let (connection, threads) = Connection::stdio();
    let result = run(connection);
    threads.join()?;
    result
}

fn run(connection: Connection) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let (initialize_id, params) = connection.initialize_start()?;
    let params: InitializeParams = serde_json::from_value(params)?;
    let encoding = choose_encoding(&params);
    let features = client_features(&params);
    let result = InitializeResult {
        capabilities: capabilities(encoding, features),
        server_info: Some(ServerInfo {
            name: "sumi-lsp".into(),
            version: Some(env!("CARGO_PKG_VERSION").into()),
        }),
    };
    connection.initialize_finish(initialize_id, serde_json::to_value(result)?)?;

    let (jobs_tx, jobs_rx) = unbounded();
    let (outcomes_tx, outcomes_rx) = unbounded();
    let worker = thread::spawn(move || worker(jobs_rx, outcomes_tx, encoding, features));
    let result = event_loop(&connection, jobs_tx, outcomes_rx, encoding, features);
    worker.join().expect("analysis worker does not panic");
    result
}

fn choose_encoding(params: &InitializeParams) -> Encoding {
    let offered = params
        .capabilities
        .general
        .as_ref()
        .and_then(|general| general.position_encodings.as_ref());
    if offered.is_some_and(|encodings| encodings.contains(&PositionEncodingKind::UTF8)) {
        Encoding::Utf8
    } else {
        Encoding::Utf16
    }
}

fn client_features(params: &InitializeParams) -> ClientFeatures {
    let text_document = &params.capabilities.text_document;
    let workspace = &params.capabilities.workspace;
    let code_action = text_document
        .as_ref()
        .and_then(|capabilities| capabilities.code_action.as_ref());
    ClientFeatures {
        code_actions: code_action
            .is_some_and(|capabilities| capabilities.code_action_literal_support.is_some())
            && workspace
                .as_ref()
                .and_then(|capabilities| capabilities.workspace_edit.as_ref())
                .is_some_and(|capabilities| capabilities.document_changes == Some(true)),
        hierarchical_symbols: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.document_symbol.as_ref())
            .is_some_and(|capabilities| {
                capabilities.hierarchical_document_symbol_support == Some(true)
            }),
        preferred_actions: code_action
            .is_some_and(|capabilities| capabilities.is_preferred_support == Some(true)),
        related_information: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.publish_diagnostics.as_ref())
            .is_some_and(|capabilities| capabilities.related_information == Some(true)),
    }
}

fn capabilities(encoding: Encoding, features: ClientFeatures) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(match encoding {
            Encoding::Utf8 => PositionEncodingKind::UTF8,
            Encoding::Utf16 => PositionEncodingKind::UTF16,
        }),
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::INCREMENTAL),
                ..TextDocumentSyncOptions::default()
            },
        )),
        code_action_provider: features.code_actions.then(|| {
            CodeActionProviderCapability::Options(CodeActionOptions {
                code_action_kinds: Some(vec![CodeActionKind::QUICKFIX]),
                ..CodeActionOptions::default()
            })
        }),
        document_formatting_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        ..ServerCapabilities::default()
    }
}

fn event_loop(
    connection: &Connection,
    jobs: Sender<Job>,
    outcomes: Receiver<Outcome>,
    encoding: Encoding,
    features: ClientFeatures,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut documents: HashMap<String, Document> = HashMap::new();
    let mut snapshots: HashMap<String, Snapshot> = HashMap::new();
    let mut next_generation = 1;
    let mut shutdown = false;
    loop {
        select! {
            recv(connection.receiver) -> message => {
                let Ok(message) = message else {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::BrokenPipe,
                        "client disconnected without an exit notification",
                    ).into());
                };
                match message {
                    Message::Request(request) => {
                        if shutdown {
                            connection.sender.send(Response::new_err(
                                request.id,
                                ErrorCode::InvalidRequest as i32,
                                "server is shutting down".into(),
                            ).into())?;
                        } else if request.method == lsp_types::request::Shutdown::METHOD {
                            connection.sender.send(Response::new_ok(request.id, ()).into())?;
                            shutdown = true;
                        } else {
                            handle_request(request, &documents, &snapshots, &jobs,
                                &connection.sender, features)?;
                        }
                    }
                    Message::Notification(notification) => {
                        if notification.method == lsp_types::notification::Exit::METHOD {
                            if shutdown {
                                return Ok(());
                            }
                            return Err(std::io::Error::other(
                                "exit notification received before shutdown",
                            ).into());
                        }
                        if !shutdown {
                            handle_notification(notification, &mut documents, &mut snapshots, &jobs,
                                &connection.sender, encoding, &mut next_generation)?;
                        }
                    }
                    Message::Response(_) => {}
                }
            }
            recv(outcomes) -> outcome => {
                let Ok(outcome) = outcome else {
                    return Err(std::io::Error::other("analysis worker disconnected").into());
                };
                if !shutdown {
                    handle_outcome(outcome, &documents, &mut snapshots, &connection.sender)?;
                }
            }
        }
    }
}

fn handle_notification(
    notification: Notification,
    documents: &mut HashMap<String, Document>,
    snapshots: &mut HashMap<String, Snapshot>,
    jobs: &Sender<Job>,
    sender: &Sender<Message>,
    encoding: Encoding,
    next_generation: &mut u64,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    match notification.method.as_str() {
        lsp_types::notification::DidOpenTextDocument::METHOD => {
            let Ok(params): Result<DidOpenTextDocumentParams, _> =
                serde_json::from_value(notification.params)
            else {
                return Ok(());
            };
            let item = params.text_document;
            let document = Document {
                generation: *next_generation,
                version: item.version,
                text: item.text,
            };
            *next_generation += 1;
            jobs.send(Job::Analyze {
                uri: item.uri.clone(),
                generation: document.generation,
                version: document.version,
                text: document.text.clone(),
            })?;
            documents.insert(item.uri.as_str().into(), document);
        }
        lsp_types::notification::DidChangeTextDocument::METHOD => {
            let Ok(params): Result<DidChangeTextDocumentParams, _> =
                serde_json::from_value(notification.params)
            else {
                return Ok(());
            };
            let uri = params.text_document.uri;
            let version = params.text_document.version;
            let Some(document) = documents.get_mut(uri.as_str()) else {
                return Ok(());
            };
            if version <= document.version {
                return Ok(());
            }
            let mut text = document.text.clone();
            for change in params.content_changes {
                if let Some(range) = change.range {
                    let positions = Positions::new(&text, encoding);
                    let Some(start) = positions.offset(range.start) else {
                        return Ok(());
                    };
                    let Some(end) = positions.offset(range.end) else {
                        return Ok(());
                    };
                    if start > end {
                        return Ok(());
                    }
                    text.replace_range(start..end, &change.text);
                } else {
                    text = change.text;
                }
            }
            document.version = version;
            document.text = text;
            snapshots.remove(uri.as_str());
            jobs.send(Job::Analyze {
                uri,
                generation: document.generation,
                version,
                text: document.text.clone(),
            })?;
        }
        lsp_types::notification::DidCloseTextDocument::METHOD => {
            let Ok(params): Result<DidCloseTextDocumentParams, _> =
                serde_json::from_value(notification.params)
            else {
                return Ok(());
            };
            let uri = params.text_document.uri;
            documents.remove(uri.as_str());
            snapshots.remove(uri.as_str());
            publish(sender, uri, None, Vec::new())?;
        }
        _ => {}
    }
    Ok(())
}

fn handle_request(
    request: Request,
    documents: &HashMap<String, Document>,
    snapshots: &HashMap<String, Snapshot>,
    jobs: &Sender<Job>,
    sender: &Sender<Message>,
    features: ClientFeatures,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    match request.method.as_str() {
        lsp_types::request::Formatting::METHOD => {
            let params: DocumentFormattingParams = match serde_json::from_value(request.params) {
                Ok(params) => params,
                Err(error) => {
                    invalid_params(sender, request.id, error)?;
                    return Ok(());
                }
            };
            queue_document_job(
                request.id,
                params.text_document.uri,
                documents,
                jobs,
                true,
                sender,
            )?;
        }
        lsp_types::request::DocumentSymbolRequest::METHOD => {
            let params: DocumentSymbolParams = match serde_json::from_value(request.params) {
                Ok(params) => params,
                Err(error) => {
                    invalid_params(sender, request.id, error)?;
                    return Ok(());
                }
            };
            queue_document_job(
                request.id,
                params.text_document.uri,
                documents,
                jobs,
                false,
                sender,
            )?;
        }
        lsp_types::request::CodeActionRequest::METHOD => {
            let params: CodeActionParams = match serde_json::from_value(request.params) {
                Ok(params) => params,
                Err(error) => {
                    invalid_params(sender, request.id, error)?;
                    return Ok(());
                }
            };
            let uri = params.text_document.uri;
            let actions = features
                .code_actions
                .then(|| {
                    documents.get(uri.as_str()).and_then(|document| {
                        snapshots
                            .get(uri.as_str())
                            .filter(|snapshot| {
                                snapshot.generation == document.generation
                                    && snapshot.version == document.version
                            })
                            .map(|snapshot| {
                                code_actions(
                                    &uri,
                                    document.version,
                                    params.range,
                                    &snapshot.fixes,
                                    features.preferred_actions,
                                )
                            })
                    })
                })
                .flatten()
                .unwrap_or_default();
            sender.send(Response::new_ok(request.id, serde_json::to_value(actions)?).into())?;
        }
        _ => sender.send(
            Response::new_err(
                request.id,
                ErrorCode::MethodNotFound as i32,
                format!("unsupported method {}", request.method),
            )
            .into(),
        )?,
    }
    Ok(())
}

fn invalid_params(
    sender: &Sender<Message>,
    id: RequestId,
    error: serde_json::Error,
) -> Result<(), crossbeam_channel::SendError<Message>> {
    sender.send(Response::new_err(id, ErrorCode::InvalidParams as i32, error.to_string()).into())
}

fn queue_document_job(
    id: RequestId,
    uri: Uri,
    documents: &HashMap<String, Document>,
    jobs: &Sender<Job>,
    format: bool,
    sender: &Sender<Message>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let Some(document) = documents.get(uri.as_str()) else {
        sender.send(Response::new_ok(id, Value::Null).into())?;
        return Ok(());
    };
    let fields = (
        id,
        uri,
        document.generation,
        document.version,
        document.text.clone(),
    );
    jobs.send(if format {
        Job::Format {
            id: fields.0,
            uri: fields.1,
            generation: fields.2,
            version: fields.3,
            text: fields.4,
        }
    } else {
        Job::Symbols {
            id: fields.0,
            uri: fields.1,
            generation: fields.2,
            version: fields.3,
            text: fields.4,
        }
    })?;
    Ok(())
}

fn worker(
    jobs: Receiver<Job>,
    outcomes: Sender<Outcome>,
    encoding: Encoding,
    features: ClientFeatures,
) {
    while let Ok(job) = jobs.recv() {
        let mut batch = vec![job];
        batch.extend(jobs.try_iter());
        let mut latest = HashMap::new();
        let mut requests = Vec::new();
        for job in batch {
            match job {
                Job::Analyze { ref uri, .. } => {
                    latest.insert(uri.as_str().to_owned(), job);
                }
                _ => requests.push(job),
            }
        }
        for job in latest.into_values().chain(requests) {
            let outcome = match job {
                Job::Analyze {
                    uri,
                    generation,
                    version,
                    text,
                } => analyze_document(
                    uri,
                    generation,
                    version,
                    text,
                    encoding,
                    features.related_information,
                ),
                Job::Format {
                    id,
                    uri,
                    generation,
                    version,
                    text,
                } => Outcome::Response {
                    id,
                    uri,
                    generation,
                    version,
                    result: serde_json::to_value(format_document(&text, encoding)).unwrap(),
                },
                Job::Symbols {
                    id,
                    uri,
                    generation,
                    version,
                    text,
                } => Outcome::Response {
                    id,
                    uri: uri.clone(),
                    generation,
                    version,
                    result: serde_json::to_value(symbols(
                        &text,
                        uri,
                        encoding,
                        features.hierarchical_symbols,
                    ))
                    .unwrap(),
                },
            };
            if outcomes.send(outcome).is_err() {
                return;
            }
        }
    }
}

fn analyze_document(
    uri: Uri,
    generation: u64,
    version: i32,
    text: String,
    encoding: Encoding,
    related_information: bool,
) -> Outcome {
    let Ok(parsed) = parse_source(text.clone().into_boxed_str()) else {
        return Outcome::Analyzed {
            uri,
            generation,
            version,
            diagnostics: Vec::new(),
            fixes: Vec::new(),
        };
    };
    let analysis = analyze(parsed);
    let positions = Positions::new(&text, encoding);
    let mut fixes = Vec::new();
    let diagnostics = analysis
        .diagnostics()
        .iter()
        .map(|diagnostic| {
            let converted = diagnostic_to_lsp(&uri, diagnostic, &positions, related_information);
            if let Some(fix) = &diagnostic.fix {
                fixes.push(fix_to_lsp(converted.clone(), fix, &positions));
            }
            converted
        })
        .collect();
    Outcome::Analyzed {
        uri,
        generation,
        version,
        diagnostics,
        fixes,
    }
}

fn diagnostic_to_lsp(
    uri: &Uri,
    diagnostic: &Diagnostic,
    positions: &Positions<'_>,
    related_information: bool,
) -> lsp_types::Diagnostic {
    lsp_types::Diagnostic {
        range: positions.range(diagnostic.primary),
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(lsp_types::NumberOrString::String(
            diagnostic.code.to_string(),
        )),
        code_description: None,
        source: Some("sumi".into()),
        message: diagnostic.message.to_string(),
        related_information: (related_information && !diagnostic.labels.is_empty()).then(|| {
            diagnostic
                .labels
                .iter()
                .map(|label| DiagnosticRelatedInformation {
                    location: Location::new(uri.clone(), positions.range(label.range)),
                    message: label.message.to_string(),
                })
                .collect()
        }),
        tags: None,
        data: None,
    }
}

fn fix_to_lsp(diagnostic: lsp_types::Diagnostic, fix: &Fix, positions: &Positions<'_>) -> LspFix {
    LspFix {
        diagnostic,
        title: fix.message.to_string(),
        edit: TextEdit::new(
            positions.range(fix.edit.range()),
            fix.edit.replacement().into(),
        ),
    }
}

fn code_actions(
    uri: &Uri,
    version: i32,
    requested: Range,
    fixes: &[LspFix],
    preferred_actions: bool,
) -> Vec<CodeActionOrCommand> {
    fixes
        .iter()
        .filter(|fix| ranges_touch(requested, fix.diagnostic.range))
        .map(|fix| {
            let edit = WorkspaceEdit {
                document_changes: Some(lsp_types::DocumentChanges::Edits(vec![TextDocumentEdit {
                    text_document: OptionalVersionedTextDocumentIdentifier {
                        uri: uri.clone(),
                        version: Some(version),
                    },
                    edits: vec![OneOf::Left(fix.edit.clone())],
                }])),
                ..WorkspaceEdit::default()
            };
            CodeActionOrCommand::CodeAction(CodeAction {
                title: fix.title.clone(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![fix.diagnostic.clone()]),
                edit: Some(edit),
                is_preferred: preferred_actions.then_some(true),
                ..CodeAction::default()
            })
        })
        .collect()
}

fn ranges_touch(left: Range, right: Range) -> bool {
    left.start <= right.end && right.start <= left.end
}

fn format_document(text: &str, encoding: Encoding) -> Option<Vec<TextEdit>> {
    let parsed = parse_source(text.to_owned().into_boxed_str()).ok()?;
    let formatted = sumi_format::format(text, parsed.lexed(), parsed.parse()).ok()?;
    let positions = Positions::new(text, encoding);
    Some(
        formatted
            .edits
            .iter()
            .map(|edit| TextEdit::new(positions.range(edit.range()), edit.replacement().into()))
            .collect(),
    )
}

fn symbols(
    text: &str,
    uri: Uri,
    encoding: Encoding,
    hierarchical: bool,
) -> Option<DocumentSymbolResponse> {
    let parsed = parse_source(text.to_owned().into_boxed_str()).ok()?;
    let analysis = analyze(parsed);
    let positions = Positions::new(text, encoding);
    if hierarchical {
        let symbols = analysis
            .functions()
            .iter()
            .filter_map(|function| {
                let name = function.name()?;
                #[allow(deprecated)]
                Some(DocumentSymbol {
                    name: name.text(text).into(),
                    detail: None,
                    kind: SymbolKind::FUNCTION,
                    tags: None,
                    deprecated: None,
                    range: positions.range(function.origin()),
                    selection_range: positions.range(name),
                    children: None,
                })
            })
            .collect();
        Some(DocumentSymbolResponse::Nested(symbols))
    } else {
        let symbols = analysis
            .functions()
            .iter()
            .filter_map(|function| {
                let name = function.name()?;
                #[allow(deprecated)]
                Some(SymbolInformation {
                    name: name.text(text).into(),
                    kind: SymbolKind::FUNCTION,
                    tags: None,
                    deprecated: None,
                    location: Location::new(uri.clone(), positions.range(function.origin())),
                    container_name: None,
                })
            })
            .collect();
        Some(DocumentSymbolResponse::Flat(symbols))
    }
}

fn handle_outcome(
    outcome: Outcome,
    documents: &HashMap<String, Document>,
    snapshots: &mut HashMap<String, Snapshot>,
    sender: &Sender<Message>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    match outcome {
        Outcome::Analyzed {
            uri,
            generation,
            version,
            diagnostics,
            fixes,
        } => {
            if documents.get(uri.as_str()).is_some_and(|document| {
                document.generation == generation && document.version == version
            }) {
                publish(sender, uri.clone(), Some(version), diagnostics)?;
                snapshots.insert(
                    uri.as_str().into(),
                    Snapshot {
                        generation,
                        version,
                        fixes,
                    },
                );
            }
        }
        Outcome::Response {
            id,
            uri,
            generation,
            version,
            result,
        } => {
            if documents.get(uri.as_str()).is_some_and(|document| {
                document.generation == generation && document.version == version
            }) {
                sender.send(Response::new_ok(id, result).into())?;
            } else {
                sender.send(
                    Response::new_err(
                        id,
                        ErrorCode::ContentModified as i32,
                        "document changed while computing the response".into(),
                    )
                    .into(),
                )?;
            }
        }
    }
    Ok(())
}

fn publish(
    sender: &Sender<Message>,
    uri: Uri,
    version: Option<i32>,
    diagnostics: Vec<lsp_types::Diagnostic>,
) -> Result<(), crossbeam_channel::SendError<Message>> {
    sender.send(
        Notification::new(
            lsp_types::notification::PublishDiagnostics::METHOD.into(),
            PublishDiagnosticsParams::new(uri, diagnostics, version),
        )
        .into(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;
    use serde_json::json;
    use std::time::Duration;

    #[test]
    fn sequential_changes_use_each_intermediate_unicode_snapshot() {
        let uri: Uri = "file:///change.su".parse().unwrap();
        let mut documents = HashMap::from([(
            uri.as_str().to_owned(),
            Document {
                generation: 1,
                version: 1,
                text: "fn main() = \"😀\"\r\n".into(),
            },
        )]);
        let mut snapshots = HashMap::from([(
            uri.as_str().to_owned(),
            Snapshot {
                generation: 1,
                version: 1,
                fixes: Vec::new(),
            },
        )]);
        let (jobs, queued) = unbounded();
        let (messages, _) = unbounded();
        let mut next_generation = 2;
        handle_notification(
            Notification::new(
                "textDocument/didChange".into(),
                json!({
                    "textDocument": { "uri": uri, "version": 2 },
                    "contentChanges": [
                        { "range": { "start": { "line": 0, "character": 13 },
                            "end": { "line": 0, "character": 15 } }, "text": "x" },
                        { "range": { "start": { "line": 0, "character": 13 },
                            "end": { "line": 0, "character": 14 } }, "text": "y" }
                    ]
                }),
            ),
            &mut documents,
            &mut snapshots,
            &jobs,
            &messages,
            Encoding::Utf16,
            &mut next_generation,
        )
        .unwrap();
        let Job::Analyze { version, text, .. } = queued.recv().unwrap() else {
            panic!("analysis job")
        };
        assert_eq!(version, 2);
        assert_eq!(text, "fn main() = \"y\"\r\n");
        assert!(!snapshots.contains_key(uri.as_str()));
    }

    #[test]
    fn oversized_columns_clamp_before_the_next_incremental_change() {
        let uri: Uri = "file:///clamp.su".parse().unwrap();
        let mut documents = HashMap::from([(
            uri.as_str().to_owned(),
            Document {
                generation: 1,
                version: 1,
                text: "a😀\r\n".into(),
            },
        )]);
        let mut snapshots = HashMap::new();
        let (jobs, queued) = unbounded();
        let (messages, _) = unbounded();
        let mut next_generation = 2;
        handle_notification(
            Notification::new(
                "textDocument/didChange".into(),
                json!({
                    "textDocument": { "uri": uri, "version": 2 },
                    "contentChanges": [
                        { "range": { "start": { "line": 0, "character": 0 },
                            "end": { "line": 0, "character": 99 } }, "text": "x" },
                        { "range": { "start": { "line": 0, "character": 1 },
                            "end": { "line": 0, "character": 99 } }, "text": "y" }
                    ]
                }),
            ),
            &mut documents,
            &mut snapshots,
            &jobs,
            &messages,
            Encoding::Utf16,
            &mut next_generation,
        )
        .unwrap();
        let Job::Analyze { text, .. } = queued.recv().unwrap() else {
            panic!("analysis job")
        };
        assert_eq!(text, "xy\r\n");
    }

    #[test]
    fn analysis_exposes_syntax_semantics_related_labels_and_fixes() {
        let uri: Uri = "file:///test.su".parse().unwrap();
        let Outcome::Analyzed {
            diagnostics, fixes, ..
        } = analyze_document(
            uri,
            1,
            7,
            "fn duplicate() = 01\nfn duplicate() = missing\n".into(),
            Encoding::Utf16,
            true,
        )
        else {
            unreachable!()
        };
        let codes: Vec<_> = diagnostics
            .iter()
            .filter_map(|diagnostic| match &diagnostic.code {
                Some(lsp_types::NumberOrString::String(code)) => Some(code.as_str()),
                _ => None,
            })
            .collect();
        assert!(codes.contains(&"syntax/noncanonical-number"));
        assert!(codes.contains(&"semantic/duplicate-name"));
        assert!(codes.contains(&"semantic/unknown-name"));
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.related_information.is_some())
        );
        assert_eq!(fixes.len(), 1);
        assert_eq!(fixes[0].edit.new_text, "1");
    }

    #[test]
    fn formatting_fixes_and_symbols_are_concrete_and_versioned() {
        let edits = format_document("fn  main()=1", Encoding::Utf16).unwrap();
        assert!(!edits.is_empty());
        let uri: Uri = "file:///test.su".parse().unwrap();
        let DocumentSymbolResponse::Nested(symbols) =
            symbols("fn main() = {", uri.clone(), Encoding::Utf16, true).unwrap()
        else {
            panic!("nested symbols")
        };
        assert_eq!(symbols[0].name, "main");

        let Outcome::Analyzed { fixes, .. } = analyze_document(
            uri.clone(),
            1,
            4,
            "fn main() = 01".into(),
            Encoding::Utf16,
            true,
        ) else {
            unreachable!()
        };
        let actions = code_actions(
            &uri,
            4,
            Range::new(Position::new(0, 0), Position::new(0, 20)),
            &fixes,
            true,
        );
        let CodeActionOrCommand::CodeAction(action) = &actions[0] else {
            unreachable!()
        };
        let Some(lsp_types::DocumentChanges::Edits(edits)) =
            &action.edit.as_ref().unwrap().document_changes
        else {
            unreachable!()
        };
        assert_eq!(edits[0].text_document.version, Some(4));
    }

    #[test]
    fn protocol_lifecycle_serves_editor_features_and_clears_on_close() {
        let (server, client) = Connection::memory();
        let server_thread = thread::spawn(move || run(server).unwrap());
        client
            .sender
            .send(
                Request::new(
                    1.into(),
                    "initialize".into(),
                    json!({
                        "capabilities": {
                            "general": { "positionEncodings": ["utf-16"] },
                            "workspace": { "workspaceEdit": { "documentChanges": true } },
                            "textDocument": {
                                "codeAction": {
                                    "codeActionLiteralSupport": {
                                        "codeActionKind": { "valueSet": ["quickfix"] }
                                    },
                                    "isPreferredSupport": true
                                },
                                "documentSymbol": {
                                    "hierarchicalDocumentSymbolSupport": true
                                },
                                "publishDiagnostics": { "relatedInformation": true }
                            }
                        }
                    }),
                )
                .into(),
            )
            .unwrap();
        let Message::Response(initialized) = receive(&client) else {
            panic!("initialize response")
        };
        let capabilities = initialized.response_result.unwrap();
        assert_eq!(capabilities["capabilities"]["positionEncoding"], "utf-16");
        assert_eq!(
            capabilities["capabilities"]["textDocumentSync"]["change"],
            2
        );
        client
            .sender
            .send(Notification::new("initialized".into(), json!({})).into())
            .unwrap();

        let uri = "file:///protocol.su";
        client
            .sender
            .send(
                Notification::new(
                    "textDocument/didOpen".into(),
                    json!({
                        "textDocument": { "uri": uri, "languageId": "sumi", "version": 1,
                            "text": "fn main() = 01" }
                    }),
                )
                .into(),
            )
            .unwrap();
        let opened = receive_diagnostics(&client);
        assert_eq!(opened.version, Some(1));
        assert!(opened.diagnostics.iter().any(|diagnostic| {
            diagnostic.code
                == Some(lsp_types::NumberOrString::String(
                    "syntax/noncanonical-number".into(),
                ))
        }));

        client
            .sender
            .send(
                Request::new(
                    2.into(),
                    "textDocument/codeAction".into(),
                    json!({
                        "textDocument": { "uri": uri },
                        "range": { "start": { "line": 0, "character": 0 },
                            "end": { "line": 0, "character": 20 } },
                        "context": { "diagnostics": opened.diagnostics }
                    }),
                )
                .into(),
            )
            .unwrap();
        let actions = response_value(&client, 2);
        assert_eq!(
            actions[0]["edit"]["documentChanges"][0]["textDocument"]["version"],
            1
        );
        assert_eq!(
            actions[0]["edit"]["documentChanges"][0]["edits"][0]["newText"],
            "1"
        );

        client
            .sender
            .send(
                Notification::new(
                    "textDocument/didChange".into(),
                    json!({
                        "textDocument": { "uri": uri, "version": 2 },
                        "contentChanges": [{ "text": "fn  main()=1" }]
                    }),
                )
                .into(),
            )
            .unwrap();
        assert_eq!(receive_diagnostics(&client).version, Some(2));

        client.sender.send(Request::new(3.into(), "textDocument/formatting".into(), json!({
            "textDocument": { "uri": uri }, "options": { "tabSize": 4, "insertSpaces": true }
        })).into()).unwrap();
        assert!(
            response_value(&client, 3)
                .as_array()
                .is_some_and(|edits| !edits.is_empty())
        );
        client
            .sender
            .send(
                Request::new(
                    4.into(),
                    "textDocument/documentSymbol".into(),
                    json!({
                        "textDocument": { "uri": uri }
                    }),
                )
                .into(),
            )
            .unwrap();
        assert_eq!(response_value(&client, 4)[0]["name"], "main");

        client
            .sender
            .send(
                Notification::new(
                    "textDocument/didChange".into(),
                    json!({
                        "textDocument": { "uri": uri, "version": 3 },
                        "contentChanges": [{ "text": "fn main() = 1" }]
                    }),
                )
                .into(),
            )
            .unwrap();
        let changed = receive_diagnostics(&client);
        assert_eq!(changed.version, Some(3));
        assert!(changed.diagnostics.is_empty());

        client
            .sender
            .send(
                Notification::new(
                    "textDocument/didClose".into(),
                    json!({
                        "textDocument": { "uri": uri }
                    }),
                )
                .into(),
            )
            .unwrap();
        let closed = receive_diagnostics(&client);
        assert_eq!(closed.version, None);
        assert!(closed.diagnostics.is_empty());

        client
            .sender
            .send(Request::new(9.into(), "shutdown".into(), Value::Null).into())
            .unwrap();
        let Message::Response(shutdown) = receive(&client) else {
            panic!("shutdown response")
        };
        assert_eq!(shutdown.id, RequestId::from(9));
        client
            .sender
            .send(Request::new(10.into(), "textDocument/formatting".into(), json!({})).into())
            .unwrap();
        let Message::Response(after_shutdown) = receive(&client) else {
            panic!("post-shutdown response")
        };
        assert_eq!(after_shutdown.id, RequestId::from(10));
        assert_eq!(
            after_shutdown.response_result.unwrap_err().code,
            ErrorCode::InvalidRequest as i32
        );
        client
            .sender
            .send(Notification::new("exit".into(), Value::Null).into())
            .unwrap();
        drop(client);
        server_thread.join().unwrap();
    }

    #[test]
    fn client_capabilities_control_response_shapes() {
        let absent: InitializeParams =
            serde_json::from_value(json!({ "capabilities": {} })).unwrap();
        let absent = client_features(&absent);
        assert!(!absent.code_actions);
        assert!(!absent.hierarchical_symbols);
        assert!(!absent.related_information);
        assert!(
            capabilities(Encoding::Utf16, absent)
                .code_action_provider
                .is_none()
        );

        let explicit_false: InitializeParams = serde_json::from_value(json!({
            "capabilities": {
                "workspace": { "workspaceEdit": { "documentChanges": false } },
                "textDocument": {
                    "codeAction": {
                        "codeActionLiteralSupport": {
                            "codeActionKind": { "valueSet": ["quickfix"] }
                        }
                    },
                    "documentSymbol": { "hierarchicalDocumentSymbolSupport": false },
                    "publishDiagnostics": { "relatedInformation": false }
                }
            }
        }))
        .unwrap();
        let explicit_false = client_features(&explicit_false);
        assert!(!explicit_false.code_actions);
        assert!(!explicit_false.hierarchical_symbols);
        assert!(!explicit_false.related_information);

        let enabled: InitializeParams = serde_json::from_value(json!({
            "capabilities": {
                "workspace": { "workspaceEdit": { "documentChanges": true } },
                "textDocument": {
                    "codeAction": {
                        "codeActionLiteralSupport": {
                            "codeActionKind": { "valueSet": ["quickfix"] }
                        },
                        "isPreferredSupport": true
                    },
                    "documentSymbol": { "hierarchicalDocumentSymbolSupport": true },
                    "publishDiagnostics": { "relatedInformation": true }
                }
            }
        }))
        .unwrap();
        let enabled = client_features(&enabled);
        assert!(enabled.code_actions);
        assert!(enabled.hierarchical_symbols);
        assert!(enabled.preferred_actions);
        assert!(enabled.related_information);

        let uri: Uri = "file:///stale.su".parse().unwrap();
        assert!(matches!(
            symbols("fn main() = 1", uri.clone(), Encoding::Utf16, false),
            Some(DocumentSymbolResponse::Flat(_))
        ));
        let Outcome::Analyzed { diagnostics, .. } = analyze_document(
            uri,
            1,
            1,
            "fn duplicate() = 1\nfn duplicate() = 2".into(),
            Encoding::Utf16,
            false,
        ) else {
            unreachable!()
        };
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_none())
        );
    }

    #[test]
    fn malformed_request_params_return_an_error() {
        let (sender, receiver) = unbounded();
        let (jobs, _) = unbounded();
        handle_request(
            Request::new(1.into(), "textDocument/formatting".into(), json!({})),
            &HashMap::new(),
            &HashMap::new(),
            &jobs,
            &sender,
            ClientFeatures {
                code_actions: false,
                hierarchical_symbols: false,
                preferred_actions: false,
                related_information: false,
            },
        )
        .unwrap();
        let Message::Response(response) = receiver.recv().unwrap() else {
            panic!("response")
        };
        assert_eq!(
            response.response_result.unwrap_err().code,
            ErrorCode::InvalidParams as i32
        );
    }

    #[test]
    fn close_and_reopen_rejects_results_from_the_old_document() {
        let (sender, receiver) = unbounded();
        let (jobs, queued) = unbounded();
        let uri: Uri = "file:///stale.su".parse().unwrap();
        let mut documents = HashMap::new();
        let mut snapshots = HashMap::new();
        let mut next_generation = 1;
        for notification in [
            Notification::new(
                "textDocument/didOpen".into(),
                json!({
                    "textDocument": { "uri": uri, "languageId": "sumi", "version": 1,
                        "text": "fn main() = 01" }
                }),
            ),
            Notification::new(
                "textDocument/didClose".into(),
                json!({ "textDocument": { "uri": uri } }),
            ),
            Notification::new(
                "textDocument/didOpen".into(),
                json!({
                    "textDocument": { "uri": uri, "languageId": "sumi", "version": 1,
                        "text": "fn main() = 42" }
                }),
            ),
        ] {
            handle_notification(
                notification,
                &mut documents,
                &mut snapshots,
                &jobs,
                &sender,
                Encoding::Utf16,
                &mut next_generation,
            )
            .unwrap();
        }
        let Job::Analyze {
            generation: old_generation,
            version: old_version,
            ..
        } = queued.recv().unwrap()
        else {
            panic!("old analysis")
        };
        let Job::Analyze {
            generation: new_generation,
            ..
        } = queued.recv().unwrap()
        else {
            panic!("new analysis")
        };
        assert_ne!(old_generation, new_generation);
        let _cleared = receiver.recv().unwrap();

        handle_outcome(
            analyze_document(
                uri.clone(),
                old_generation,
                old_version,
                "fn main() = 01".into(),
                Encoding::Utf16,
                true,
            ),
            &documents,
            &mut snapshots,
            &sender,
        )
        .unwrap();
        assert!(receiver.try_recv().is_err());
        assert!(!snapshots.contains_key(uri.as_str()));

        handle_outcome(
            Outcome::Response {
                id: 2.into(),
                uri,
                generation: old_generation,
                version: old_version,
                result: json!([]),
            },
            &documents,
            &mut snapshots,
            &sender,
        )
        .unwrap();
        let Message::Response(response) = receiver.recv().unwrap() else {
            panic!("response")
        };
        assert_eq!(
            response.response_result.unwrap_err().code,
            ErrorCode::ContentModified as i32
        );
    }

    #[test]
    fn exit_without_shutdown_is_an_error() {
        let (server, client) = Connection::memory();
        let server_thread = thread::spawn(move || run(server));
        client
            .sender
            .send(
                Request::new(
                    1.into(),
                    "initialize".into(),
                    json!({
                        "capabilities": {}
                    }),
                )
                .into(),
            )
            .unwrap();
        let Message::Response(_) = receive(&client) else {
            panic!("initialize response")
        };
        client
            .sender
            .send(Notification::new("exit".into(), Value::Null).into())
            .unwrap();
        assert!(server_thread.join().unwrap().is_err());
    }

    fn receive(client: &Connection) -> Message {
        client
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .unwrap()
    }

    fn receive_diagnostics(client: &Connection) -> PublishDiagnosticsParams {
        let Message::Notification(notification) = receive(client) else {
            panic!("diagnostics")
        };
        assert_eq!(notification.method, "textDocument/publishDiagnostics");
        serde_json::from_value(notification.params).unwrap()
    }

    fn response_value(client: &Connection, id: i32) -> Value {
        let Message::Response(response) = receive(client) else {
            panic!("response")
        };
        assert_eq!(response.id, RequestId::from(id));
        response.response_result.unwrap()
    }
}
