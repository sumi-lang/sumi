fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    sumi_lsp::run_stdio()
}
