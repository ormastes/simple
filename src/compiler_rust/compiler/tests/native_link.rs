//! End-to-end native compilation test: compile .spl files to object code, then link.
//!
//! This test compiles each .spl file separately through:
//!   Parse -> Mono -> HIR -> MIR -> Cranelift Codegen -> .o file
//! Then links all .o files together into a native binary.
//!
//! Environment variables:
//! * `SRC_COMPILER_DIR` - directory to scan (default: src/compiler/)
//! * `NATIVE_LINK_LIMIT` - max files to compile (default: 50 for speed)

use std::path::{Path, PathBuf};

use simple_compiler::codegen::Codegen;
use simple_compiler::hir::Lowerer;
use simple_compiler::linker::LinkerBuilder;
use simple_compiler::module_resolver::ModuleResolver;
use simple_compiler::monomorphize::monomorphize_module;

const STACK_SIZE: usize = 16 * 1024 * 1024;

fn project_root() -> PathBuf {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    crate_dir
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .expect("could not find project root")
        .to_path_buf()
}

fn compile_file_to_object(source: &str, file_path: &Path) -> Result<Vec<u8>, String> {
    // Parse
    let mut parser = simple_parser::Parser::new(source);
    let ast = parser.parse().map_err(|e| format!("parse: {e}"))?;

    // Mono
    let ast = monomorphize_module(&ast);

    // HIR
    let root = project_root();
    let source_root = root.join("src");
    let resolver = ModuleResolver::new(root.clone(), source_root);
    let mut lowerer = Lowerer::with_module_resolver(resolver, file_path.to_path_buf());
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).map_err(|e| format!("hir: {e}"))?;

    // MIR
    let mir = simple_compiler::mir::lower_to_mir(&hir).map_err(|e| format!("mir: {e}"))?;

    // Codegen
    let codegen = Codegen::new().map_err(|e| format!("codegen init: {e}"))?;
    let obj = codegen.compile_module(&mir).map_err(|e| format!("codegen: {e}"))?;

    Ok(obj)
}

fn compile_file_safe(source: String, file_path: PathBuf) -> Result<Vec<u8>, String> {
    let handle = std::thread::Builder::new()
        .name("compile-worker".into())
        .stack_size(STACK_SIZE)
        .spawn(move || compile_file_to_object(&source, &file_path))
        .expect("spawn failed");

    match handle.join() {
        Ok(result) => result,
        Err(e) => {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                format!("panic: {s}")
            } else if let Some(s) = e.downcast_ref::<&str>() {
                format!("panic: {s}")
            } else {
                "panic: unknown".to_string()
            };
            Err(msg)
        }
    }
}

fn collect_spl_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_recursive(dir, &mut files);
    files.sort();
    files
}

fn collect_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_recursive(&path, out);
        } else if path.extension().map_or(false, |e| e == "spl") {
            out.push(path);
        }
    }
}

#[test]
fn compile_and_link_native() {
    let root = project_root();
    let compiler_dir = std::env::var("SRC_COMPILER_DIR")
        .unwrap_or_else(|_| root.join("src/compiler").to_string_lossy().into_owned());
    let limit: usize = std::env::var("NATIVE_LINK_LIMIT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(50);

    let dir = PathBuf::from(&compiler_dir);
    assert!(dir.is_dir(), "not found: {}", dir.display());

    let all_files = collect_spl_files(&dir);
    let files: Vec<_> = all_files.iter().take(limit).collect();
    eprintln!("\n=== Native Link Test: {} files (limit {}) ===", files.len(), limit);

    // Phase 1: Compile each file to object code
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let mut object_paths = Vec::new();
    let mut compile_ok = 0usize;
    let mut compile_fail = 0usize;

    for (i, path) in files.iter().enumerate() {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => { compile_fail += 1; continue; }
        };

        match compile_file_safe(source, path.to_path_buf()) {
            Ok(obj_code) => {
                let obj_path = temp_dir.path().join(format!("mod_{}.o", i));
                std::fs::write(&obj_path, &obj_code).expect("write .o");
                object_paths.push(obj_path);
                compile_ok += 1;
            }
            Err(e) => {
                let rel = path.strip_prefix(&root).unwrap_or(path);
                eprintln!("  FAIL {}: {}", rel.display(), e);
                compile_fail += 1;
            }
        }

        if (i + 1) % 10 == 0 {
            eprintln!("  [{}/{}] compiled", i + 1, files.len());
        }
    }

    eprintln!("\nCompiled: {}/{} ({} failed)", compile_ok, files.len(), compile_fail);
    eprintln!("Object files: {} in {}", object_paths.len(), temp_dir.path().display());

    if object_paths.is_empty() {
        eprintln!("No object files to link, skipping link phase");
        return;
    }

    // Show total object code size
    let total_size: u64 = object_paths.iter()
        .filter_map(|p| std::fs::metadata(p).ok())
        .map(|m| m.len())
        .sum();
    eprintln!("Total object code: {} KB", total_size / 1024);

    // Phase 2: Link object files together
    let output_path = temp_dir.path().join("simple_native");
    eprintln!("\nLinking {} objects -> {}", object_paths.len(), output_path.display());

    // Find the Simple runtime library
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()  // compiler_rust
        .to_path_buf();
    let runtime_a = {
        let candidates = [
            workspace_root.join("target/debug/libsimple_runtime.a"),
            workspace_root.join("target/debug/deps/libsimple_runtime.a"),
            workspace_root.join("target/release/libsimple_runtime.a"),
            workspace_root.join("target/release/deps/libsimple_runtime.a"),
        ];
        let fallback = candidates[0].clone();
        candidates.into_iter().find(|p| p.exists()).unwrap_or(fallback)
    };
    if runtime_a.exists() {
        eprintln!("Using runtime: {}", runtime_a.display());
    } else {
        eprintln!("WARNING: Runtime not found at {}", runtime_a.display());
    }

    // Write a minimal main() stub
    let main_c = temp_dir.path().join("main_stub.c");
    std::fs::write(&main_c, "int main(int argc, char** argv) { return 0; }\n").expect("write main stub");

    // Compile main stub
    let main_o = temp_dir.path().join("main_stub.o");
    let cc = std::env::var("CC").unwrap_or_else(|_| {
        if std::process::Command::new("clang").arg("--version").output().is_ok() {
            "clang".to_string()
        } else {
            "gcc".to_string()
        }
    });

    let stub_status = std::process::Command::new(&cc)
        .args(["-c", "-o"])
        .arg(&main_o)
        .arg(&main_c)
        .status()
        .expect("compile main stub");
    assert!(stub_status.success(), "failed to compile main stub");

    let mut cmd = std::process::Command::new(&cc);
    cmd.arg("-o").arg(&output_path);
    cmd.arg("-pie");

    // Main stub first
    cmd.arg(&main_o);

    // Add object files
    for obj in &object_paths {
        cmd.arg(obj);
    }

    // Add runtime library
    if runtime_a.exists() {
        cmd.arg(&runtime_a);
    }

    // System libraries
    cmd.args(["-lpthread", "-ldl", "-lm", "-llzma"]);

    eprintln!("Link command: {:?}", cmd);

    match cmd.output() {
        Ok(output) => {
            if output.status.success() {
                let size = std::fs::metadata(&output_path).map(|m| m.len()).unwrap_or(0);
                eprintln!("Link SUCCESS: {} ({} KB)", output_path.display(), size / 1024);

                // Try to run the binary (should fail gracefully - no main)
                match std::process::Command::new(&output_path).arg("--version").output() {
                    Ok(run) => {
                        eprintln!("Run exit code: {}", run.status);
                        if !run.stdout.is_empty() {
                            eprintln!("stdout: {}", String::from_utf8_lossy(&run.stdout));
                        }
                    }
                    Err(e) => eprintln!("Run failed: {}", e),
                }
            } else {
                let stderr = String::from_utf8_lossy(&output.stderr);
                eprintln!("Link FAILED (exit {}): {}", output.status, stderr);
                // Show first few undefined symbols if any
                let undef_lines: Vec<&str> = stderr.lines()
                    .filter(|l| l.contains("undefined"))
                    .take(10)
                    .collect();
                if !undef_lines.is_empty() {
                    eprintln!("\nUndefined symbols ({}):", undef_lines.len());
                    for line in &undef_lines {
                        eprintln!("  {}", line);
                    }
                }
            }
        }
        Err(e) => eprintln!("Failed to invoke {}: {}", cc, e),
    }
}
