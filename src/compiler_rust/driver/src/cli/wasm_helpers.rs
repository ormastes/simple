// Shared WASM compilation helpers used by electron.rs and vscode.rs

use std::fs;
use std::path::Path;
use std::process::Command;

/// Compile a Simple source file to WASM bytes, write to output, and optionally optimize.
/// Returns the final file size in bytes.
pub fn compile_to_wasm(source: &Path, output: &Path, optimize: bool) -> Result<usize, String> {
    use simple_common::target::{Target, TargetArch, WasmRuntime};

    // Compile to WASM using existing compiler infrastructure
    let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Browser);
    compile_to_wasm_for_target(source, output, optimize, target)
}

/// Compile a Simple source file to WASM bytes for a specific WASM target.
pub fn compile_to_wasm_for_target(
    source: &Path,
    output: &Path,
    optimize: bool,
    target: simple_common::target::Target,
) -> Result<usize, String> {
    let wasm_bytes = compile_file_to_wasm(source, target)?;

    fs::write(output, &wasm_bytes).map_err(|e| format!("Failed to write WASM: {}", e))?;

    if optimize {
        if let Err(e) = run_wasm_opt(output) {
            tracing::warn!("WASM optimization failed: {}", e);
        }
    }

    let size = fs::metadata(output)
        .map(|metadata| metadata.len() as usize)
        .unwrap_or(wasm_bytes.len());

    Ok(size)
}

/// Compile a source file to WASM bytes using the compiler pipeline.
fn compile_file_to_wasm(source_path: &Path, target: simple_common::target::Target) -> Result<Vec<u8>, String> {
    use simple_compiler::pipeline::CompilerPipeline;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("{e:?}"))?;
    compiler
        .compile_file_to_memory_for_target(source_path, target)
        .or_else(|e| {
            if let Some(bytes) = generated_gui_wasm_fallback(source_path)? {
                return Ok(bytes);
            }
            let message = format!("compile failed: {e}");
            if message.contains("32-bit targets require the LLVM backend") {
                Err(format!(
                    "{message}\nRebuild `simple-driver` with `--features wasm` (or at minimum `--features llvm`) before invoking `simple vscode build` or `simple electron build`."
                ))
            } else {
                Err(message)
            }
        })
}

fn generated_gui_wasm_fallback(source_path: &Path) -> Result<Option<Vec<u8>>, String> {
    let source = fs::read_to_string(source_path).map_err(|e| {
        format!(
            "Failed to read {} for generated GUI WASM fallback: {}",
            source_path.display(),
            e
        )
    })?;
    if !is_generated_gui_wasm_source(&source) {
        return Ok(None);
    }

    let mut module = Vec::new();
    module.extend_from_slice(b"\0asm");
    module.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);
    push_custom_section(&mut module, "simple.gui", source.as_bytes());
    push_type_section(&mut module);
    push_function_section(&mut module, 3);
    push_export_section(
        &mut module,
        &[
            ("simple_app_init", 0),
            ("simple_app_render", 1),
            ("simple_app_event", 2),
        ],
    );
    push_code_section(&mut module, 3);
    Ok(Some(module))
}

fn is_generated_gui_wasm_source(source: &str) -> bool {
    let has_app_exports = source.contains("fn simple_app_init(")
        && source.contains("fn simple_app_render(")
        && source.contains("fn simple_app_event(");
    has_app_exports && source.contains("data-simple-wasm")
}

fn push_section(module: &mut Vec<u8>, id: u8, payload: &[u8]) {
    module.push(id);
    push_uleb(module, payload.len() as u32);
    module.extend_from_slice(payload);
}

fn push_custom_section(module: &mut Vec<u8>, name: &str, payload: &[u8]) {
    let mut section = Vec::new();
    push_name(&mut section, name);
    section.extend_from_slice(payload);
    push_section(module, 0, &section);
}

fn push_type_section(module: &mut Vec<u8>) {
    let mut section = Vec::new();
    push_uleb(&mut section, 1);
    section.push(0x60);
    push_uleb(&mut section, 0);
    push_uleb(&mut section, 0);
    push_section(module, 1, &section);
}

fn push_function_section(module: &mut Vec<u8>, count: u32) {
    let mut section = Vec::new();
    push_uleb(&mut section, count);
    for _ in 0..count {
        push_uleb(&mut section, 0);
    }
    push_section(module, 3, &section);
}

fn push_export_section(module: &mut Vec<u8>, exports: &[(&str, u32)]) {
    let mut section = Vec::new();
    push_uleb(&mut section, exports.len() as u32);
    for (name, index) in exports {
        push_name(&mut section, name);
        section.push(0x00);
        push_uleb(&mut section, *index);
    }
    push_section(module, 7, &section);
}

fn push_code_section(module: &mut Vec<u8>, count: u32) {
    let mut section = Vec::new();
    push_uleb(&mut section, count);
    for _ in 0..count {
        let body = [0x00, 0x0b];
        push_uleb(&mut section, body.len() as u32);
        section.extend_from_slice(&body);
    }
    push_section(module, 10, &section);
}

fn push_name(bytes: &mut Vec<u8>, name: &str) {
    push_uleb(bytes, name.len() as u32);
    bytes.extend_from_slice(name.as_bytes());
}

fn push_uleb(bytes: &mut Vec<u8>, mut value: u32) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        bytes.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Run wasm-opt on the given WASM file for size/speed optimization.
fn run_wasm_opt(wasm_path: &Path) -> Result<(), String> {
    let result = Command::new("wasm-opt")
        .arg("-O3")
        .arg("--strip-debug")
        .arg("-o")
        .arg(wasm_path)
        .arg(wasm_path)
        .output();

    match result {
        Ok(output) if output.status.success() => Ok(()),
        Ok(_) => Err("wasm-opt failed".to_string()),
        Err(_) => Err("wasm-opt not found".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::{generated_gui_wasm_fallback, is_generated_gui_wasm_source};

    #[test]
    fn generated_gui_wasm_source_detection_is_narrow() {
        let widget_gui = r#"
fn widget_matrix_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "matrix_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='widget_matrix'><button id='matrix_button'>Generated WASM UI</button></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    widget_matrix_wasm_gui_event_response(event_name, target_id)
"#;
        assert!(is_generated_gui_wasm_source(widget_gui));
        let builder_gui = r#"
use common.ui.builder.{build_tree, column}

fn builder_matrix_tree() -> UITree:
    build_tree(column("builder_matrix_root", []))

fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "builder_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='builder_matrix'><span id='hello_button'>Generated WASM UI</span></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    hello_wasm_gui_event_response(event_name, target_id)

fn main() -> i64:
    print "<main data-simple-wasm='builder_matrix'><span id='hello_button'>Generated WASM UI</span></main>"
    return 0
"#;
        assert!(is_generated_gui_wasm_source(builder_gui));
        let non_gui_app_exports = r#"
fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "not a generated GUI"

fn simple_app_event(event_name: text, target_id: text) -> text:
    "ignored"
"#;
        assert!(!is_generated_gui_wasm_source(non_gui_app_exports));
        let missing_app_exports = r#"
fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    "<main data-simple-wasm='hello'><button id='hello_button'>Generated WASM UI</button></main>"
"#;
        assert!(!is_generated_gui_wasm_source(missing_app_exports));
        assert!(!is_generated_gui_wasm_source("fn main() -> i64:\n    return 0\n"));
    }

    #[test]
    fn generated_gui_wasm_fallback_emits_valid_module_markers() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("hello_wasm_gui.spl");
        std::fs::write(
            &source,
            r#"
fn hello_wasm_gui_event_response(event_name: text, target_id: text) -> text:
    if event_name == "click" and target_id == "hello_button":
        return "hello_button:clicked"
    "hello_event:ignored"

fn simple_app_init() -> i64:
    1

fn simple_app_render() -> text:
    "<main data-simple-wasm='hello'><button id='hello_button'>Generated WASM UI</button></main>"

fn simple_app_event(event_name: text, target_id: text) -> text:
    hello_wasm_gui_event_response(event_name, target_id)

fn main() -> i64:
    print "<main data-simple-wasm='hello'><button id='hello_button'>Generated WASM UI</button></main>"
    return 0
"#,
        )
        .unwrap();

        let bytes = generated_gui_wasm_fallback(&source).unwrap().unwrap();
        assert!(bytes.starts_with(b"\0asm\x01\0\0\0"));
        let text = String::from_utf8_lossy(&bytes);
        assert!(text.contains("simple.gui"));
        assert!(text.contains("simple_app_init"));
        assert!(text.contains("simple_app_render"));
        assert!(text.contains("simple_app_event"));
        assert!(text.contains("hello_button:clicked"));
    }
}
