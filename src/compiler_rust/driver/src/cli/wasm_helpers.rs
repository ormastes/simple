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
        .map_err(|e| {
            let message = format!("compile failed: {e}");
            if message.contains("32-bit targets require the LLVM backend") {
                format!(
                    "{message}\nRebuild `simple-driver` with `--features wasm` (or at minimum `--features llvm`) before invoking `simple vscode build` or `simple electron build`."
                )
            } else {
                message
            }
        })
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
