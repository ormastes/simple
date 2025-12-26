//! Web Framework Compiler
//!
//! Multi-target compilation for .sui files with server/client separation.
//!
//! # Architecture
//!
//! ```text
//! .sui file → SuiParser → [Server Blocks, Client Blocks, Templates]
//!                              ↓              ↓              ↓
//!                         Compile x64    Compile wasm32   Generate HTML
//!                              ↓              ↓              ↓
//!                         example.so     example.wasm    example.html
//! ```
//!
//! # Example
//!
//! ```ignore
//! use simple_compiler::web_compiler::WebCompiler;
//! use simple_common::target::{Target, TargetArch, WasmRuntime};
//!
//! let compiler = WebCompiler::new()?;
//! let result = compiler.compile_sui_file("app.sui")?;
//!
//! // result.server_binary - Compiled server code (x64 native)
//! // result.client_binary - Compiled client code (wasm32)
//! // result.template_html - Rendered template
//! ```

use crate::error::CompileError;
use crate::pipeline::CompilerPipeline;
use crate::hydration_manifest::{HydrationManifest, ManifestBuilder, ManifestMetadata};
use simple_common::target::{Target, TargetArch, TargetOS, WasmRuntime};
use simple_parser::sui_parser::{SuiParser, SuiFile, ClientBlock, ServerBlock};
use std::path::Path;

/// Result of compiling a .sui file
#[derive(Debug)]
pub struct SuiCompilationResult {
    /// Compiled server code (native x64 or JIT bytecode)
    pub server_binary: Vec<u8>,
    /// Compiled client code (wasm32-unknown-unknown)
    pub client_binary: Vec<u8>,
    /// Rendered HTML template
    pub template_html: String,
    /// Exported client functions for hydration
    pub client_exports: Vec<String>,
    /// Hydration manifest for client-side event binding
    pub hydration_manifest: HydrationManifest,
    /// Generated hydration JavaScript code
    pub hydration_script: String,
}

/// Web framework compiler for .sui files
pub struct WebCompiler {
    /// Compiler pipeline for native/JIT compilation
    pipeline: CompilerPipeline,
}

impl WebCompiler {
    /// Create a new web compiler
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self {
            pipeline: CompilerPipeline::new()?,
        })
    }

    /// Compile a .sui file from source string
    pub fn compile_sui_source(&mut self, source: &str) -> Result<SuiCompilationResult, CompileError> {
        // Parse .sui file
        let mut parser = SuiParser::new(source.to_string());
        let sui_file = parser.parse()
            .map_err(|e| CompileError::Parse(format!("Failed to parse .sui file: {}", e)))?;

        // Compile server and client blocks
        self.compile_sui_file_parsed(sui_file)
    }

    /// Compile a .sui file from path
    pub fn compile_sui_file(&mut self, path: impl AsRef<Path>) -> Result<SuiCompilationResult, CompileError> {
        let source = std::fs::read_to_string(path.as_ref())
            .map_err(|e| CompileError::Io(format!("Failed to read .sui file: {}", e)))?;

        self.compile_sui_source(&source)
    }

    /// Compile a parsed .sui file
    fn compile_sui_file_parsed(&mut self, sui_file: SuiFile) -> Result<SuiCompilationResult, CompileError> {
        // Extract all client exports
        let client_exports = sui_file.client_blocks.iter()
            .flat_map(|block| block.exports.iter().cloned())
            .collect::<Vec<_>>();

        // Compile server blocks
        let server_binary = if !sui_file.server_blocks.is_empty() {
            self.compile_server_blocks(&sui_file.server_blocks)?
        } else {
            vec![]
        };

        // Compile client blocks
        let client_binary = if !sui_file.client_blocks.is_empty() {
            self.compile_client_blocks(&sui_file.client_blocks)?
        } else {
            vec![]
        };

        // Render templates (simple concatenation for now)
        let mut template_html = sui_file.template_blocks.iter()
            .map(|block| block.template.clone())
            .collect::<Vec<_>>()
            .join("\n");

        // Generate hydration manifest
        let hydration_manifest = self.generate_hydration_manifest(&sui_file, client_binary.len());

        // Generate hydration script
        let hydration_script = hydration_manifest.generate_hydration_script();

        // Inject hydration script into template if client code exists
        if !client_binary.is_empty() {
            template_html = self.inject_hydration_into_template(
                &template_html,
                &hydration_script,
                "app" // Default module name
            );
        }

        Ok(SuiCompilationResult {
            server_binary,
            client_binary,
            template_html,
            client_exports,
            hydration_manifest,
            hydration_script,
        })
    }

    /// Compile server blocks to native x64 code
    fn compile_server_blocks(&mut self, blocks: &[ServerBlock]) -> Result<Vec<u8>, CompileError> {
        // Combine all server blocks into one module
        let combined_code = self.combine_blocks(blocks);

        // Compile to host architecture (x64)
        let target = Target::host();

        self.pipeline.compile_source_to_memory_for_target(&combined_code, target)
    }

    /// Compile client blocks to wasm32 code
    fn compile_client_blocks(&mut self, blocks: &[ClientBlock]) -> Result<Vec<u8>, CompileError> {
        // Combine all client blocks into one module
        let combined_code = self.combine_client_blocks(blocks);

        // Compile to wasm32-unknown-unknown
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Browser);

        self.pipeline.compile_source_to_memory_for_target(&combined_code, target)
    }

    /// Combine server blocks into a single source string
    fn combine_blocks(&self, blocks: &[ServerBlock]) -> String {
        blocks.iter()
            .enumerate()
            .map(|(i, block)| {
                let comment = if let Some(ref label) = block.label {
                    format!("# Server block: {}\n", label)
                } else {
                    format!("# Server block {}\n", i)
                };
                format!("{}{}\n", comment, block.code)
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Combine client blocks into a single source string
    fn combine_client_blocks(&self, blocks: &[ClientBlock]) -> String {
        blocks.iter()
            .enumerate()
            .map(|(i, block)| {
                let comment = if let Some(ref label) = block.label {
                    format!("# Client block: {}\n", label)
                } else {
                    format!("# Client block {}\n", i)
                };
                format!("{}{}\n", comment, block.code)
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Generate hydration manifest from client blocks
    fn generate_hydration_manifest(&self, sui_file: &SuiFile, wasm_size: usize) -> HydrationManifest {
        let mut builder = ManifestBuilder::new();

        // Add all client exports
        for export in &sui_file.client_blocks.iter().flat_map(|b| &b.exports).cloned().collect::<Vec<_>>() {
            builder = builder.with_export(export);
        }

        // Parse client code to extract event bindings
        // For now, we'll use a simple heuristic: look for addEventListener calls
        for block in &sui_file.client_blocks {
            let bindings = self.extract_event_bindings(&block.code);
            for (selector, event, handler) in bindings {
                builder = builder.with_binding(selector, event, handler);
            }
        }

        // Add shared state from server blocks
        for state_decl in &sui_file.shared_state {
            // Use parsed name and initializer
            if let Some(ref init_value) = state_decl.initializer {
                builder = builder.with_state(&state_decl.name, init_value);
            }
        }

        // Add metadata
        let metadata = ManifestMetadata {
            compiled_at: chrono::Utc::now().to_rfc3339(),
            source: "sui_file".to_string(),
            wasm_size: Some(wasm_size),
        };
        builder = builder.with_metadata(metadata);

        builder.build()
    }

    /// Extract event bindings from client code
    /// Looks for patterns like: element.addEventListener("event", handler)
    fn extract_event_bindings(&self, code: &str) -> Vec<(String, String, String)> {
        let mut bindings = Vec::new();

        // Simple regex-based extraction (can be improved with proper parsing)
        // Pattern: getElementById("id").addEventListener("event", handler)
        for line in code.lines() {
            if let Some(pos) = line.find("addEventListener") {
                // Extract selector (look for getElementById before addEventListener)
                let before = &line[..pos];
                let selector = if let Some(id_start) = before.rfind("getElementById(") {
                    let id_part = &before[id_start + 15..]; // Skip 'getElementById('
                    // Find opening quote
                    if let Some(quote_start) = id_part.find('"') {
                        let after_quote = &id_part[quote_start + 1..];
                        // Find closing quote
                        if let Some(quote_end) = after_quote.find('"') {
                            format!("#{}", &after_quote[..quote_end])
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                } else if let Some(qs_start) = before.rfind("querySelector(") {
                    let qs_part = &before[qs_start + 14..]; // Skip 'querySelector('
                    // Find opening quote
                    if let Some(quote_start) = qs_part.find('"') {
                        let after_quote = &qs_part[quote_start + 1..];
                        // Find closing quote
                        if let Some(quote_end) = after_quote.find('"') {
                            after_quote[..quote_end].to_string()
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

                // Extract event and handler
                let after = &line[pos + 16..]; // Skip "addEventListener"
                if let Some(paren_start) = after.find('(') {
                    let args = &after[paren_start + 1..];

                    // Parse arguments: "event", handler
                    let parts: Vec<&str> = args.split(',').collect();
                    if parts.len() >= 2 {
                        // Event name (strip quotes)
                        let event = parts[0].trim().trim_matches('"').to_string();

                        // Handler name (strip whitespace and parentheses)
                        let handler = parts[1].trim().trim_end_matches(')').trim().to_string();

                        bindings.push((selector, event, handler));
                    }
                }
            }
        }

        bindings
    }

    /// Inject hydration script into HTML template
    ///
    /// If template has a </body> tag, inject before it.
    /// Otherwise, wrap template in a complete HTML document.
    fn inject_hydration_into_template(&self, template: &str, hydration_script: &str, wasm_module_name: &str) -> String {
        let wasm_loader = self.generate_wasm_loader(wasm_module_name, hydration_script);

        // Check if template has a closing </body> tag
        if let Some(body_end_pos) = template.rfind("</body>") {
            // Inject script before </body>
            let before = &template[..body_end_pos];
            let after = &template[body_end_pos..];
            format!("{}\n{}\n{}", before, wasm_loader, after)
        } else if let Some(html_end_pos) = template.rfind("</html>") {
            // No </body> but has </html>, inject before </html>
            let before = &template[..html_end_pos];
            let after = &template[html_end_pos..];
            format!("{}\n{}\n{}", before, wasm_loader, after)
        } else {
            // No closing tags, wrap in complete HTML document
            self.wrap_in_html_document(template, &wasm_loader)
        }
    }

    /// Generate WASM module loader script
    fn generate_wasm_loader(&self, module_name: &str, hydration_script: &str) -> String {
        format!(r#"<script type="module">
// WASM Module Loader and Hydration
{}

// Load WASM module
async function loadWasm() {{
    try {{
        const response = await fetch('./{}.wasm');
        const wasmBuffer = await response.arrayBuffer();
        const wasmModule = await WebAssembly.instantiate(wasmBuffer, {{}});
        return wasmModule.instance.exports;
    }} catch (error) {{
        console.error('Failed to load WASM module:', error);
        return null;
    }}
}}

// Initialize application
async function init() {{
    const wasm = await loadWasm();
    if (wasm) {{
        await hydrate(wasm);
    }} else {{
        console.error('WASM hydration skipped due to load failure');
    }}
}}

// Auto-initialize when DOM is ready
if (document.readyState === 'loading') {{
    document.addEventListener('DOMContentLoaded', init);
}} else {{
    init();
}}
</script>"#, hydration_script, module_name)
    }

    /// Wrap template in complete HTML document
    fn wrap_in_html_document(&self, template: &str, wasm_loader: &str) -> String {
        format!(r#"<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Simple WASM App</title>
</head>
<body>
{}
{}
</body>
</html>"#, template, wasm_loader)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_web_compiler_creation() {
        let compiler = WebCompiler::new();
        assert!(compiler.is_ok());
    }

    #[test]
    fn test_compile_simple_sui_file() {
        let source = r#"
{- server -}
fn get_count() -> i64:
    return 42

{+ client +}
fn increment() -> i64:
    return 1

{@ render @}
<div>Hello World</div>
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        // Should succeed parsing
        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should have template HTML
        assert!(compiled.template_html.contains("Hello World"));

        // Should have client exports
        assert_eq!(compiled.client_exports.len(), 1);
        assert_eq!(compiled.client_exports[0], "increment");
    }

    #[test]
    fn test_compile_server_only() {
        let source = r#"
{- server -}
fn main() -> i64:
    return 42
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should have server binary
        assert!(!compiled.server_binary.is_empty());

        // Should have empty client binary
        assert!(compiled.client_binary.is_empty());

        // Should have empty template
        assert!(compiled.template_html.is_empty());
    }

    #[test]
    fn test_compile_client_only() {
        let source = r#"
{+ client +}
fn on_click() -> i64:
    return 1
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should have empty server binary
        assert!(compiled.server_binary.is_empty());

        // Should have client binary (if wasm compilation succeeds)
        // Note: May fail if LLVM wasm backend not available

        // Should have client exports
        assert_eq!(compiled.client_exports.len(), 1);
        assert_eq!(compiled.client_exports[0], "on_click");
    }

    #[test]
    fn test_combine_multiple_blocks() {
        let source = r#"
{- init -}
fn init() -> i64:
    return 1

{- process -}
fn process() -> i64:
    return 2

{+ client +}
fn handler1() -> i64:
    return 3

{+ client +}
fn handler2() -> i64:
    return 4
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        if let Err(ref e) = result {
            eprintln!("Compilation error: {:?}", e);
        }

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should combine multiple server blocks
        // Should combine multiple client blocks

        // Should have both handler exports
        assert_eq!(compiled.client_exports.len(), 2);
        assert!(compiled.client_exports.contains(&"handler1".to_string()));
        assert!(compiled.client_exports.contains(&"handler2".to_string()));
    }

    #[test]
    fn test_template_rendering() {
        let source = r#"
{@ header @}
<header>Site Header</header>

{@ body @}
<main>Content</main>

{@ footer @}
<footer>Footer</footer>
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should combine all templates
        assert!(compiled.template_html.contains("Site Header"));
        assert!(compiled.template_html.contains("Content"));
        assert!(compiled.template_html.contains("Footer"));
    }

    #[test]
    fn test_hydration_manifest_generation() {
        let source = r#"
{$ let count: i64 = 0 $}

{+ client +}
fn on_click() -> i64:
    return 1

{@ render @}
<button id="btn">Click me</button>
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        if let Err(ref e) = result {
            eprintln!("Hydration manifest test error: {:?}", e);
        }

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Check hydration manifest
        assert_eq!(compiled.hydration_manifest.version, 2);

        // Should have client exports
        assert!(compiled.hydration_manifest.exports.contains(&"on_click".to_string()));

        // State parsing not yet implemented in sui_parser, so state may be empty
        // This will work once SharedStateDecl parsing is complete

        // Should have hydration script
        assert!(compiled.hydration_script.contains("export async function hydrate(wasm)"));

        // Should have metadata
        assert!(compiled.hydration_manifest.metadata.is_some());
        if let Some(ref metadata) = compiled.hydration_manifest.metadata {
            assert_eq!(metadata.source, "sui_file");
        }

        // Should be able to serialize to JSON
        let json = compiled.hydration_manifest.to_json();
        assert!(json.is_ok());
        let json_str = json.unwrap();
        assert!(json_str.contains("\"version\": 2"));
        assert!(json_str.contains("on_click"));
    }

    #[test]
    fn test_extract_event_bindings() {
        let compiler = WebCompiler::new().unwrap();

        let code = r#"
dom.getElementById("submit-btn").addEventListener("click", handle_submit)
dom.querySelector(".menu-item").addEventListener("mouseover", show_menu)
"#;

        let bindings = compiler.extract_event_bindings(code);

        assert_eq!(bindings.len(), 2);

        assert_eq!(bindings[0].0, "#submit-btn");
        assert_eq!(bindings[0].1, "click");
        assert_eq!(bindings[0].2, "handle_submit");

        assert_eq!(bindings[1].0, ".menu-item");
        assert_eq!(bindings[1].1, "mouseover");
        assert_eq!(bindings[1].2, "show_menu");
    }

    #[test]
    fn test_inject_hydration_before_body_tag() {
        let compiler = WebCompiler::new().unwrap();
        let template = r#"<html>
<body>
<h1>Hello</h1>
</body>
</html>"#;
        let hydration_script = "export async function hydrate(wasm) { }";

        let result = compiler.inject_hydration_into_template(template, hydration_script, "test_app");

        assert!(result.contains("<h1>Hello</h1>"));
        assert!(result.contains("<script type=\"module\">"));
        assert!(result.contains("async function hydrate(wasm)"));
        assert!(result.contains("fetch('./test_app.wasm')"));

        // Script should be before </body>
        let script_pos = result.find("<script").unwrap();
        let body_end_pos = result.find("</body>").unwrap();
        assert!(script_pos < body_end_pos);
    }

    #[test]
    fn test_inject_hydration_before_html_tag() {
        let compiler = WebCompiler::new().unwrap();
        let template = r#"<html>
<h1>Hello</h1>
</html>"#;
        let hydration_script = "export async function hydrate(wasm) { }";

        let result = compiler.inject_hydration_into_template(template, hydration_script, "test_app");

        assert!(result.contains("<h1>Hello</h1>"));
        assert!(result.contains("<script type=\"module\">"));

        // Script should be before </html>
        let script_pos = result.find("<script").unwrap();
        let html_end_pos = result.find("</html>").unwrap();
        assert!(script_pos < html_end_pos);
    }

    #[test]
    fn test_wrap_template_in_html_document() {
        let compiler = WebCompiler::new().unwrap();
        let template = "<h1>Hello World</h1>";
        let hydration_script = "export async function hydrate(wasm) { }";

        let result = compiler.inject_hydration_into_template(template, hydration_script, "test_app");

        assert!(result.contains("<!DOCTYPE html>"));
        assert!(result.contains("<html lang=\"en\">"));
        assert!(result.contains("<head>"));
        assert!(result.contains("<meta charset=\"UTF-8\">"));
        assert!(result.contains("<body>"));
        assert!(result.contains("<h1>Hello World</h1>"));
        assert!(result.contains("<script type=\"module\">"));
        assert!(result.contains("</body>"));
        assert!(result.contains("</html>"));
    }

    #[test]
    fn test_generate_wasm_loader() {
        let compiler = WebCompiler::new().unwrap();
        let hydration_script = r#"export async function hydrate(wasm) {
    console.log('Hydrating');
}"#;

        let result = compiler.generate_wasm_loader("my_app", hydration_script);

        assert!(result.contains("<script type=\"module\">"));
        assert!(result.contains("export async function hydrate(wasm)"));
        assert!(result.contains("fetch('./my_app.wasm')"));
        assert!(result.contains("WebAssembly.instantiate"));
        assert!(result.contains("await hydrate(wasm)"));
        assert!(result.contains("DOMContentLoaded"));
        assert!(result.contains("</script>"));
    }

    #[test]
    fn test_complete_sui_compilation_with_injection() {
        let source = r#"
{+ client +}
fn on_click() -> i64:
    return 1

{@ render @}
<html>
<body>
<button id="btn">Click me</button>
</body>
</html>
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should have client binary
        assert!(!compiled.client_binary.is_empty());

        // Template should have injected script
        assert!(compiled.template_html.contains("<button id=\"btn\">Click me</button>"));
        assert!(compiled.template_html.contains("<script type=\"module\">"));
        assert!(compiled.template_html.contains("async function hydrate(wasm)"));
        assert!(compiled.template_html.contains("fetch('./app.wasm')"));

        // Script should be before </body>
        let script_pos = compiled.template_html.find("<script").unwrap();
        let body_end_pos = compiled.template_html.find("</body>").unwrap();
        assert!(script_pos < body_end_pos);
    }

    #[test]
    fn test_sui_compilation_without_client_blocks() {
        let source = r#"
{- server -}
fn main() -> i64:
    return 42

{@ render @}
<h1>Server Only</h1>
"#;

        let mut compiler = WebCompiler::new().unwrap();
        let result = compiler.compile_sui_source(source);

        assert!(result.is_ok());

        let compiled = result.unwrap();

        // Should NOT inject script if no client code
        assert!(!compiled.template_html.contains("<script type=\"module\">"));
        assert!(compiled.template_html.contains("<h1>Server Only</h1>"));
    }
}
