use std::collections::HashMap;
use std::thread;

use crossbeam_channel::{Receiver, Sender, select, unbounded};
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::Notification as _;
use lsp_types::request::Request as _;
use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOptions, CodeActionOrCommand, CodeActionParams,
    CodeActionProviderCapability, CompletionItem, CompletionItemKind, CompletionList,
    CompletionOptions, CompletionParams, DiagnosticRelatedInformation, DiagnosticSeverity,
    DiagnosticTag, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DocumentFormattingParams, DocumentSymbol, DocumentSymbolParams,
    DocumentSymbolResponse, InitializeParams, InitializeResult, InsertTextFormat, Location, OneOf,
    OptionalVersionedTextDocumentIdentifier, Position, PositionEncodingKind,
    PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo, SymbolInformation, SymbolKind,
    TextDocumentEdit, TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TextEdit, Uri, WorkspaceEdit,
};
use serde_json::Value;
use sumi_frontend::{Diagnostic, Fix, Severity, parse_source};
use sumi_hir::{Analysis, BindingKind, Dead, DeadCause, Signature, Ty, analyze};
use sumi_lexer::{Fixed, LexedFile, RawIdx, SyntaxKind};
use sumi_syntax::ast::{self, AstNode, View};
use sumi_syntax::{NodeKind, SyntaxTree, starts_statement};
use sumi_text::{Encoding, TextSize};

use crate::position::Positions;

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
    has_code_actions: bool,
    has_hierarchical_symbols: bool,
    has_preferred_actions: bool,
    has_related_information: bool,
    has_snippets: bool,
    has_unnecessary_tags: bool,
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
    Complete {
        id: RequestId,
        uri: Uri,
        generation: u64,
        version: i32,
        text: String,
        position: Position,
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
        has_code_actions: code_action
            .is_some_and(|capabilities| capabilities.code_action_literal_support.is_some())
            && workspace
                .as_ref()
                .and_then(|capabilities| capabilities.workspace_edit.as_ref())
                .is_some_and(|capabilities| capabilities.document_changes == Some(true)),
        has_hierarchical_symbols: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.document_symbol.as_ref())
            .is_some_and(|capabilities| {
                capabilities.hierarchical_document_symbol_support == Some(true)
            }),
        has_preferred_actions: code_action
            .is_some_and(|capabilities| capabilities.is_preferred_support == Some(true)),
        has_related_information: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.publish_diagnostics.as_ref())
            .is_some_and(|capabilities| capabilities.related_information == Some(true)),
        has_snippets: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.completion.as_ref())
            .and_then(|capabilities| capabilities.completion_item.as_ref())
            .is_some_and(|capabilities| capabilities.snippet_support == Some(true)),
        has_unnecessary_tags: text_document
            .as_ref()
            .and_then(|capabilities| capabilities.publish_diagnostics.as_ref())
            .and_then(|capabilities| capabilities.tag_support.as_ref())
            .is_some_and(|tags| tags.value_set.contains(&DiagnosticTag::UNNECESSARY)),
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
        code_action_provider: features.has_code_actions.then(|| {
            CodeActionProviderCapability::Options(CodeActionOptions {
                code_action_kinds: Some(vec![CodeActionKind::QUICKFIX]),
                ..CodeActionOptions::default()
            })
        }),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            ..CompletionOptions::default()
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
    let mut is_shut_down = false;
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
                        if is_shut_down {
                            connection.sender.send(Response::new_err(
                                request.id,
                                ErrorCode::InvalidRequest as i32,
                                "server is shutting down".into(),
                            ).into())?;
                        } else if request.method == lsp_types::request::Shutdown::METHOD {
                            connection.sender.send(Response::new_ok(request.id, ()).into())?;
                            is_shut_down = true;
                        } else {
                            handle_request(request, &documents, &snapshots, &jobs,
                                &connection.sender, features)?;
                        }
                    }
                    Message::Notification(notification) => {
                        if notification.method == lsp_types::notification::Exit::METHOD {
                            if is_shut_down {
                                return Ok(());
                            }
                            return Err(std::io::Error::other(
                                "exit notification received before shutdown",
                            ).into());
                        }
                        if !is_shut_down {
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
                if !is_shut_down {
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
        lsp_types::request::Completion::METHOD => {
            let params: CompletionParams = match serde_json::from_value(request.params) {
                Ok(params) => params,
                Err(error) => {
                    invalid_params(sender, request.id, error)?;
                    return Ok(());
                }
            };
            let uri = params.text_document_position.text_document.uri;
            let Some(document) = documents.get(uri.as_str()) else {
                sender.send(Response::new_ok(request.id, Value::Null).into())?;
                return Ok(());
            };
            jobs.send(Job::Complete {
                id: request.id,
                uri,
                generation: document.generation,
                version: document.version,
                text: document.text.clone(),
                position: params.text_document_position.position,
            })?;
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
                .has_code_actions
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
                                    features.has_preferred_actions,
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
    should_format: bool,
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
    jobs.send(if should_format {
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
                    features.has_related_information,
                    features.has_unnecessary_tags,
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
                        features.has_hierarchical_symbols,
                    ))
                    .unwrap(),
                },
                Job::Complete {
                    id,
                    uri,
                    generation,
                    version,
                    text,
                    position,
                } => Outcome::Response {
                    id,
                    uri,
                    generation,
                    version,
                    result: serde_json::to_value(complete(
                        &text,
                        position,
                        encoding,
                        features.has_snippets,
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
    has_related_information: bool,
    has_unnecessary_tags: bool,
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
            let mut converted =
                diagnostic_to_lsp(&uri, diagnostic, &positions, has_related_information);
            // Unreachable code's warning spans exactly the dead statements, so it carries the tag.
            let after_stop = Dead {
                range: diagnostic.primary,
                cause: DeadCause::AfterStop,
            };
            if has_unnecessary_tags && analysis.dead().contains(&after_stop) {
                converted.tags = Some(vec![DiagnosticTag::UNNECESSARY]);
            }
            if let Some(fix) = &diagnostic.fix {
                fixes.push(fix_to_lsp(converted.clone(), fix, &positions));
            }
            converted
        })
        // A constant condition's warning spans the condition, so its dead code gets its own hint.
        .chain(
            analysis
                .dead()
                .iter()
                .filter(|dead| has_unnecessary_tags && dead.cause != DeadCause::AfterStop)
                .map(|dead| dead_to_lsp(dead, &positions)),
        )
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
    has_related_information: bool,
) -> lsp_types::Diagnostic {
    lsp_types::Diagnostic {
        range: positions.range(diagnostic.primary),
        severity: Some(match diagnostic.code.severity {
            Severity::Error => DiagnosticSeverity::ERROR,
            Severity::Warning => DiagnosticSeverity::WARNING,
        }),
        code: Some(lsp_types::NumberOrString::String(
            diagnostic.code.to_string(),
        )),
        code_description: None,
        source: Some("sumi".into()),
        message: diagnostic.message.to_string(),
        related_information: (has_related_information && !diagnostic.labels.is_empty()).then(
            || {
                diagnostic
                    .labels
                    .iter()
                    .map(|label| DiagnosticRelatedInformation {
                        location: Location::new(uri.clone(), positions.range(label.range)),
                        message: label.message.to_string(),
                    })
                    .collect()
            },
        ),
        tags: None,
        data: None,
    }
}

fn dead_to_lsp(dead: &Dead, positions: &Positions<'_>) -> lsp_types::Diagnostic {
    lsp_types::Diagnostic {
        range: positions.range(dead.range),
        severity: Some(DiagnosticSeverity::HINT),
        source: Some("sumi".into()),
        message: dead.cause.to_string(),
        tags: Some(vec![DiagnosticTag::UNNECESSARY]),
        ..lsp_types::Diagnostic::default()
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
    has_preferred_actions: bool,
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
                is_preferred: has_preferred_actions.then_some(true),
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
    is_hierarchical: bool,
) -> Option<DocumentSymbolResponse> {
    let parsed = parse_source(text.to_owned().into_boxed_str()).ok()?;
    let analysis = analyze(parsed);
    let positions = Positions::new(text, encoding);
    if is_hierarchical {
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

/// What a name typed at a position can be.
enum Context {
    /// A comment, a literal, or a declaration taking a new name.
    Nothing,
    /// Between items.
    Items,
    /// After `:` or `->`.
    Types,
    /// A single keyword the grammar admits next.
    Keyword(Fixed),
    /// An expression or a statement, with `else` when an `if`'s block just closed.
    Values { has_else: bool },
}

fn context(lexed: &LexedFile, tree: &SyntaxTree, offset: TextSize) -> Context {
    let significant = |until: RawIdx| {
        RawIdx::new(0)
            .until(until)
            .rev()
            .find(|&index| !lexed.kind(index).is_trivia())
    };
    let adjacent =
        |left: RawIdx, right: RawIdx| lexed.range(left).end() == lexed.range(right).start();
    let is_word = |kind: SyntaxKind| kind == SyntaxKind::Ident || is_keyword(kind);
    let Some(before) = offset
        .to_u32()
        .checked_sub(1)
        .and_then(|offset| lexed.token_at(TextSize::new(offset)))
    else {
        return Context::Items;
    };
    let kind = lexed.kind(before);
    let (gap_end, previous) = if is_word(kind) {
        (before, significant(before))
    } else if kind.is_trivia() {
        if kind == SyntaxKind::LineComment {
            return Context::Nothing;
        }
        (before + 1, significant(before))
    } else if kind == SyntaxKind::IntLiteral || kind == SyntaxKind::Error {
        return Context::Nothing;
    } else {
        (before, Some(before))
    };
    let Some(previous) = previous else {
        return Context::Items;
    };
    // A whole item ends at its closing brace or at the line break after its last token; one the
    // parser recovered in is still being typed, whatever its last token.
    let has_line_break = (previous + 1)
        .until(gap_end)
        .any(|index| lexed.kind(index) == SyntaxKind::Newline);
    let at_item_level = ast::SourceFile::cast(tree, tree.root())
        .expect("the root is a file")
        .items(tree)
        .any(|item| {
            let node = item.node();
            previous + 1 == tree.end_token(node)
                && !tree.has_error(node)
                && (lexed.kind(previous) == SyntaxKind::RBrace || has_line_break)
        });
    let is_inside = |kinds: &[NodeKind]| {
        tree.nodes().any(|node| {
            kinds.contains(&tree.kind(node))
                && tree.first_token(node) <= previous
                && previous < tree.end_token(node)
        })
    };
    let earlier = significant(previous);
    match lexed.kind(previous) {
        SyntaxKind::FnKw | SyntaxKind::ForKw | SyntaxKind::MutKw => Context::Nothing,
        SyntaxKind::LetKw => Context::Keyword(Fixed::MutKw),
        SyntaxKind::Colon => Context::Types,
        SyntaxKind::Gt
            if earlier.is_some_and(|earlier| {
                lexed.kind(earlier) == SyntaxKind::Minus && adjacent(earlier, previous)
            }) =>
        {
            Context::Types
        }
        SyntaxKind::Ident
            if earlier.is_some_and(|earlier| lexed.kind(earlier) == SyntaxKind::ForKw) =>
        {
            Context::Keyword(Fixed::InKw)
        }
        _ if is_inside(&[NodeKind::ParamList, NodeKind::TypeRef]) => Context::Nothing,
        _ if at_item_level => Context::Items,
        _ => Context::Values {
            has_else: lexed.kind(previous) == SyntaxKind::RBrace
                && tree.nodes().any(|node| {
                    ast::IfExpr::cast(tree, node).is_some_and(|branch| {
                        branch.else_branch(tree).is_none()
                            && branch
                                .then_branch(tree)
                                .is_some_and(|then| tree.end_token(then.node()) == previous + 1)
                    })
                }),
        },
    }
}

fn is_keyword(kind: SyntaxKind) -> bool {
    kind.text()
        .is_some_and(|text| SyntaxKind::from_keyword(text) == Some(kind))
}

fn complete(
    text: &str,
    position: Position,
    encoding: Encoding,
    has_snippets: bool,
) -> Option<CompletionList> {
    let positions = Positions::new(text, encoding);
    let offset = TextSize::new(u32::try_from(positions.offset(position)?).ok()?);
    let parsed = parse_source(text.to_owned().into_boxed_str()).ok()?;
    let analysis = analyze(parsed);
    let lexed = analysis.parsed().lexed();
    let tree = analysis.parsed().parse().tree();
    let keyword = |fixed: Fixed| CompletionItem {
        label: fixed.text().into(),
        kind: Some(CompletionItemKind::KEYWORD),
        sort_text: Some(format!("2{}", fixed.text())),
        ..CompletionItem::default()
    };
    let items = match context(lexed, tree, offset) {
        Context::Nothing => Vec::new(),
        Context::Items => vec![keyword(Fixed::FnKw)],
        Context::Types => Ty::ALL
            .iter()
            .map(|ty| CompletionItem {
                label: ty.as_str().into(),
                kind: Some(CompletionItemKind::STRUCT),
                ..CompletionItem::default()
            })
            .collect(),
        Context::Keyword(fixed) => vec![keyword(fixed)],
        Context::Values { has_else } => {
            let mut items = values(&analysis, offset, has_snippets);
            items.extend(
                SyntaxKind::ALL
                    .iter()
                    .filter_map(|kind| kind.fixed())
                    .filter(|fixed| {
                        is_keyword(fixed.kind())
                            && (starts_statement(fixed.kind())
                                || (has_else && *fixed == Fixed::ElseKw))
                    })
                    .map(keyword),
            );
            items
        }
    };
    Some(CompletionList {
        is_incomplete: false,
        items,
    })
}

/// The locals visible at `offset`, then every function, each with its type.
fn values(analysis: &Analysis, offset: TextSize, has_snippets: bool) -> Vec<CompletionItem> {
    let text = analysis.parsed().source();
    let mut items: Vec<_> = analysis
        .visible_at(offset)
        .into_iter()
        .map(|binding| {
            let name = binding.name().text(text);
            let ty = analysis.ty(binding.declaration()).map(|ty| ty.as_str());
            let detail = match (binding.kind(), ty) {
                (BindingKind::Let { is_mutable: true }, Some(ty)) => Some(format!("mut {ty}")),
                (BindingKind::Let { is_mutable: true }, None) => Some("mut".into()),
                (_, ty) => ty.map(String::from),
            };
            CompletionItem {
                label: name.into(),
                kind: Some(CompletionItemKind::VARIABLE),
                detail,
                sort_text: Some(format!("0{name}")),
                ..CompletionItem::default()
            }
        })
        .collect();
    items.extend(analysis.functions().iter().filter_map(|function| {
        let name = function.name()?.text(text);
        let signature = function.signature();
        let (insert_text, insert_text_format) = match signature {
            Some(Signature { params, .. }) if params.is_empty() => {
                (Some(format!("{name}()")), None)
            }
            Some(_) if has_snippets => {
                (Some(format!("{name}($0)")), Some(InsertTextFormat::SNIPPET))
            }
            _ => (None, None),
        };
        Some(CompletionItem {
            label: name.into(),
            kind: Some(CompletionItemKind::FUNCTION),
            detail: signature.map(|Signature { params, result }| {
                let params: Vec<_> = params.iter().map(|ty| ty.as_str()).collect();
                format!("fn({}) -> {result}", params.join(", "))
            }),
            insert_text,
            insert_text_format,
            sort_text: Some(format!("1{name}")),
            ..CompletionItem::default()
        })
    }));
    items
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
                text: "fn main() = 😀\r\n".into(),
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
                        { "range": { "start": { "line": 0, "character": 12 },
                            "end": { "line": 0, "character": 14 } }, "text": "x" },
                        { "range": { "start": { "line": 0, "character": 12 },
                            "end": { "line": 0, "character": 13 } }, "text": "y" }
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
        assert_eq!(text, "fn main() = y\r\n");
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
            false,
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
    fn dead_code_is_tagged_unnecessary_over_exactly_its_range() {
        let text = "fn branch() -> int = if false { 1 } else { 2 }
fn right(b: bool) -> bool = false && b
fn body() -> int {
    let mut total = 0
    for i in 5..5 {
        total = total + i
    }
    total
}
fn after() -> int {
    return 1
    let x = 2
    x
}
fn main() -> bool = right(true)";
        let analyzed = |has_unnecessary_tags| {
            let uri: Uri = "file:///dead.su".parse().unwrap();
            let Outcome::Analyzed { diagnostics, .. } = analyze_document(
                uri,
                1,
                1,
                text.into(),
                Encoding::Utf16,
                false,
                has_unnecessary_tags,
            ) else {
                unreachable!()
            };
            diagnostics
        };
        let range = |start: (u32, u32), end: (u32, u32)| {
            Range::new(Position::new(start.0, start.1), Position::new(end.0, end.1))
        };
        let tagged: Vec<_> = analyzed(true)
            .into_iter()
            .filter(|diagnostic| diagnostic.tags == Some(vec![DiagnosticTag::UNNECESSARY]))
            .map(|diagnostic| {
                (
                    diagnostic.range,
                    diagnostic.severity.unwrap(),
                    diagnostic.message,
                )
            })
            .collect();
        assert_eq!(
            tagged,
            [
                (
                    range((11, 4), (12, 5)),
                    DiagnosticSeverity::WARNING,
                    "unreachable code".into()
                ),
                (
                    range((0, 30), (0, 35)),
                    DiagnosticSeverity::HINT,
                    "this branch never runs".into()
                ),
                (
                    range((1, 37), (1, 38)),
                    DiagnosticSeverity::HINT,
                    "the right side never runs".into()
                ),
                (
                    range((4, 18), (6, 5)),
                    DiagnosticSeverity::HINT,
                    "the loop body never runs".into()
                ),
            ]
        );
        let untagged = analyzed(false);
        assert!(untagged.iter().all(|diagnostic| diagnostic.tags.is_none()
            && diagnostic.severity != Some(DiagnosticSeverity::HINT)));
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
            false,
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

    fn labels(text: &str, line: u32, character: u32, has_snippets: bool) -> Vec<String> {
        let list = complete(
            text,
            Position::new(line, character),
            Encoding::Utf16,
            has_snippets,
        )
        .unwrap();
        let mut items = list.items;
        items.sort_by(|a, b| a.sort_text.cmp(&b.sort_text));
        items.into_iter().map(|item| item.label).collect()
    }

    #[test]
    fn completion_offers_what_the_position_admits() {
        let text = "fn add(a: int, b: int) -> int = a + b
fn body(c: bool) -> int {
    let c = if c { 1 } else { 0 }
    let mut total = 0
    for i in 0..c {
        if i > 1 { total = 1 }
        total = total + i
    }
    // total
    tot
}
";
        let statement_keywords = ["_", "false", "for", "if", "let", "return", "true"];
        let values = |locals: &[&str], has_else: bool| -> Vec<String> {
            let mut locals = locals.to_vec();
            locals.sort_unstable();
            let mut keywords = statement_keywords.to_vec();
            if has_else {
                keywords.push("else");
            }
            keywords.sort_unstable();
            locals
                .into_iter()
                .chain(["add", "body"])
                .chain(keywords)
                .map(String::from)
                .collect()
        };
        assert_eq!(labels(text, 0, 0, false), ["fn"]);
        assert_eq!(labels(text, 11, 0, false), ["fn"]);
        assert_eq!(labels(text, 1, 3, false), Vec::<String>::new());
        assert_eq!(labels(text, 1, 8, false), Vec::<String>::new());
        assert_eq!(labels(text, 1, 16, false), Vec::<String>::new());
        assert_eq!(labels(text, 1, 24, false), Vec::<String>::new());
        assert_eq!(labels(text, 2, 8, false), ["mut"]);
        assert_eq!(labels(text, 4, 8, false), Vec::<String>::new());
        assert_eq!(labels(text, 4, 10, false), ["in"]);
        assert_eq!(labels(text, 1, 11, false), ["int", "bool", "unit"]);
        assert_eq!(labels(text, 1, 23, false), ["int", "bool", "unit"]);
        assert_eq!(labels(text, 8, 9, false), Vec::<String>::new());
        assert_eq!(labels(text, 3, 21, false), Vec::<String>::new());
        assert_eq!(labels(text, 2, 15, false), values(&["c"], false));
        assert_eq!(labels(text, 2, 22, false), values(&["c"], false));
        assert_eq!(
            labels(text, 5, 30, false),
            values(&["c", "total", "i"], true)
        );
        assert_eq!(
            labels(text, 6, 24, false),
            values(&["c", "total", "i"], false)
        );
        assert_eq!(labels(text, 8, 0, false), values(&["c", "total"], false));
        assert_eq!(labels(text, 9, 7, false), values(&["c", "total"], false));

        let list = complete(text, Position::new(9, 7), Encoding::Utf16, true).unwrap();
        let item = |label: &str| list.items.iter().find(|item| item.label == label).unwrap();
        assert_eq!(item("total").detail.as_deref(), Some("mut int"));
        assert_eq!(item("c").detail.as_deref(), Some("int"));
        assert_eq!(item("c").kind, Some(CompletionItemKind::VARIABLE));
        assert_eq!(item("add").detail.as_deref(), Some("fn(int, int) -> int"));
        assert_eq!(item("add").insert_text.as_deref(), Some("add($0)"));
        assert_eq!(
            item("add").insert_text_format,
            Some(InsertTextFormat::SNIPPET)
        );
        assert_eq!(item("body").insert_text.as_deref(), Some("body($0)"));
        let list = complete(text, Position::new(9, 7), Encoding::Utf16, false).unwrap();
        let add = list.items.iter().find(|item| item.label == "add").unwrap();
        assert_eq!(add.insert_text, None);
        let list = complete(
            "fn zero() = 0\nfn f() = ze",
            Position::new(1, 10),
            Encoding::Utf16,
            false,
        )
        .unwrap();
        let zero = list.items.iter().find(|item| item.label == "zero").unwrap();
        assert_eq!(zero.insert_text.as_deref(), Some("zero()"));
        assert_eq!(zero.insert_text_format, None);
    }

    #[test]
    fn completion_survives_recovery() {
        let keywords = ["_", "false", "for", "if", "let", "return", "true"];
        let values = |locals: &[&str], has_else: bool| -> Vec<String> {
            let mut keywords = keywords.to_vec();
            if has_else {
                keywords.push("else");
            }
            keywords.sort_unstable();
            locals
                .iter()
                .copied()
                .chain(["f"])
                .chain(keywords)
                .map(String::from)
                .collect()
        };
        let text = "fn f(x: int) -> int {\n    let y = \n    let z = x +\n    ";
        assert_eq!(labels(text, 3, 4, false), values(&["x", "y", "z"], false));
        let text = "fn f(x: int) -> int {\n    if x > 0 { x }\n    ";
        assert_eq!(labels(text, 2, 4, false), values(&["x"], true));
        assert_eq!(
            labels("fn f(x: int) -> int = ", 0, 22, false),
            values(&["x"], false)
        );
        assert_eq!(labels("fn f(", 0, 5, false), Vec::<String>::new());
        assert_eq!(labels("fn f(a: int, ", 0, 13, false), Vec::<String>::new());
        assert_eq!(labels("fn f(a: int) ", 0, 13, false), Vec::<String>::new());
        assert_eq!(
            labels("fn f(a: int) -> int ", 0, 20, false),
            Vec::<String>::new()
        );
        let text = "fn f() = {\n    if true { let q = 1 } \n}";
        assert_eq!(labels(text, 1, 26, false), values(&[], true));
        assert_eq!(labels(text, 1, 24, false), values(&["q"], false));
        assert_eq!(labels("", 0, 0, false), ["fn"]);
        assert_eq!(
            complete("", Position::new(3, 0), Encoding::Utf16, false),
            None
        );
    }

    #[test]
    fn protocol_completes_with_the_client_snippet_support() {
        let (client, server_thread) = start(json!({
            "textDocument": { "completion": { "completionItem": { "snippetSupport": true } } }
        }));
        let uri = "file:///complete.su";
        open(
            &client,
            uri,
            "fn double(x: int) -> int = x + x\nfn main() -> int {\n    let total = 1\n    tot\n}\n",
        );
        let at =
            json!({ "textDocument": { "uri": uri }, "position": { "line": 3, "character": 7 } });
        let list = request(&client, 1, "textDocument/completion", at).unwrap();
        let labels: Vec<_> = list["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item["label"].as_str().unwrap().to_owned())
            .collect();
        assert!(labels.contains(&"total".to_owned()));
        let double = list["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["label"] == "double")
            .unwrap();
        assert_eq!(double["insertText"], "double($0)");
        assert_eq!(double["insertTextFormat"], 2);
        let unopened = json!({
            "textDocument": { "uri": "file:///other.su" },
            "position": { "line": 0, "character": 0 }
        });
        assert_eq!(
            request(&client, 2, "textDocument/completion", unopened).unwrap(),
            Value::Null
        );
        let error = request(&client, 3, "textDocument/completion", json!({})).unwrap_err();
        assert_eq!(error.code, ErrorCode::InvalidParams as i32);
        stop(client, server_thread);
    }

    #[test]
    fn client_capabilities_control_response_shapes() {
        let absent: InitializeParams =
            serde_json::from_value(json!({ "capabilities": {} })).unwrap();
        let absent = client_features(&absent);
        assert!(!absent.has_code_actions);
        assert!(!absent.has_hierarchical_symbols);
        assert!(!absent.has_related_information);
        assert!(!absent.has_snippets);
        assert!(!absent.has_unnecessary_tags);
        let offered = capabilities(Encoding::Utf16, absent);
        assert!(offered.code_action_provider.is_none());
        assert!(offered.completion_provider.is_some());

        let explicit_false: InitializeParams = serde_json::from_value(json!({
            "capabilities": {
                "workspace": { "workspaceEdit": { "documentChanges": false } },
                "textDocument": {
                    "codeAction": {
                        "codeActionLiteralSupport": {
                            "codeActionKind": { "valueSet": ["quickfix"] }
                        }
                    },
                    "completion": { "completionItem": { "snippetSupport": false } },
                    "documentSymbol": { "hierarchicalDocumentSymbolSupport": false },
                    "publishDiagnostics": { "relatedInformation": false }
                }
            }
        }))
        .unwrap();
        let explicit_false = client_features(&explicit_false);
        assert!(!explicit_false.has_code_actions);
        assert!(!explicit_false.has_hierarchical_symbols);
        assert!(!explicit_false.has_related_information);
        assert!(!explicit_false.has_snippets);
        assert!(!explicit_false.has_unnecessary_tags);

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
                    "completion": { "completionItem": { "snippetSupport": true } },
                    "documentSymbol": { "hierarchicalDocumentSymbolSupport": true },
                    "publishDiagnostics": {
                        "relatedInformation": true,
                        "tagSupport": { "valueSet": [1] }
                    }
                }
            }
        }))
        .unwrap();
        let enabled = client_features(&enabled);
        assert!(enabled.has_code_actions);
        assert!(enabled.has_hierarchical_symbols);
        assert!(enabled.has_preferred_actions);
        assert!(enabled.has_related_information);
        assert!(enabled.has_snippets);
        assert!(enabled.has_unnecessary_tags);

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
                has_code_actions: false,
                has_hierarchical_symbols: false,
                has_preferred_actions: false,
                has_related_information: false,
                has_snippets: false,
                has_unnecessary_tags: false,
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
                false,
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

    /// A server over an in-memory connection, initialized with `capabilities`.
    fn start(capabilities: Value) -> (Connection, thread::JoinHandle<()>) {
        let (server, client) = Connection::memory();
        let server_thread = thread::spawn(move || run(server).unwrap());
        let params = json!({ "capabilities": capabilities });
        client
            .sender
            .send(Request::new(0.into(), "initialize".into(), params).into())
            .unwrap();
        let Message::Response(_) = receive(&client) else {
            panic!("initialize response")
        };
        client
            .sender
            .send(Notification::new("initialized".into(), json!({})).into())
            .unwrap();
        (client, server_thread)
    }

    fn stop(client: Connection, server_thread: thread::JoinHandle<()>) {
        client
            .sender
            .send(Request::new(99.into(), "shutdown".into(), Value::Null).into())
            .unwrap();
        let Message::Response(_) = receive(&client) else {
            panic!("shutdown response")
        };
        client
            .sender
            .send(Notification::new("exit".into(), Value::Null).into())
            .unwrap();
        drop(client);
        server_thread.join().unwrap();
    }

    fn notify(client: &Connection, method: &str, params: Value) {
        client
            .sender
            .send(Notification::new(method.into(), params).into())
            .unwrap();
    }

    fn open(client: &Connection, uri: &str, text: &str) -> PublishDiagnosticsParams {
        notify(
            client,
            "textDocument/didOpen",
            json!({
                "textDocument": { "uri": uri, "languageId": "sumi", "version": 1, "text": text }
            }),
        );
        receive_diagnostics(client)
    }

    fn request(
        client: &Connection,
        id: i32,
        method: &str,
        params: Value,
    ) -> Result<Value, lsp_server::ResponseError> {
        client
            .sender
            .send(Request::new(id.into(), method.into(), params).into())
            .unwrap();
        let Message::Response(response) = receive(client) else {
            panic!("response to {method}")
        };
        assert_eq!(response.id, RequestId::from(id));
        response.response_result
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
