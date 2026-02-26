//! Batch C compilation test for src/compiler/ .spl files.
//!
//! Reads each .spl file in the specified compiler source directory (default:
//! `src/compiler/00.common/`), then runs it through each stage of the Rust
//! bootstrap pipeline:
//!
//!   1. Parse  (simple_parser)
//!   2. Monomorphize  (monomorphize_module)
//!   3. HIR lower  (hir::lower)
//!   4. MIR lower  (mir::lower_to_mir)
//!   5. C codegen  (CCodegen::compile_module)
//!
//! A summary table is printed showing pass/fail counts per stage plus
//! per-file failure details.
//!
//! ## Environment variables
//!
//! * `SRC_COMPILER_DIR` - directory to scan for `.spl` files.
//!   Defaults to `src/compiler/00.common` relative to the project root.
//! * `SRC_COMPILER_DIR_ALL` - directory to scan for the all-layers test.
//!   Not set by default; set to `src/compiler/` (project root) to run.

use std::path::{Path, PathBuf};

use simple_compiler::codegen::CCodegen;
use simple_compiler::hir;
use simple_compiler::mir;
use simple_compiler::monomorphize::monomorphize_module;

/// Stack size for pipeline threads (16 MB) to handle deeply nested files.
const PIPELINE_STACK_SIZE: usize = 16 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Per-file result tracking
// ---------------------------------------------------------------------------

/// Which pipeline stage a file reached before failing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[allow(dead_code)]
enum Stage {
    Parse,
    Mono,
    Hir,
    Mir,
    CCodegen,
    /// All stages passed.
    Done,
}

impl Stage {
    fn label(&self) -> &'static str {
        match self {
            Stage::Parse => "Parse",
            Stage::Mono => "Mono",
            Stage::Hir => "HIR",
            Stage::Mir => "MIR",
            Stage::CCodegen => "C",
            Stage::Done => "Done",
        }
    }
}

struct FileResult {
    path: PathBuf,
    /// The stage that *failed*. If `error` is None, all stages passed.
    reached: Stage,
    error: Option<String>,
}

impl FileResult {
    fn passed(&self, stage: Stage) -> bool {
        if self.error.is_none() {
            // All stages passed.
            return true;
        }
        // The file failed at `self.reached`. It passed all stages *before* that.
        self.reached > stage
    }
}

// ---------------------------------------------------------------------------
// Pipeline runner
// ---------------------------------------------------------------------------

fn run_pipeline(source: &str) -> (Stage, Option<String>) {
    // 1. Parse
    let mut parser = simple_parser::Parser::new(source);
    let ast_module = match parser.parse() {
        Ok(m) => m,
        Err(e) => return (Stage::Parse, Some(format!("{e}"))),
    };

    // 2. Monomorphize (infallible)
    let ast_module = monomorphize_module(&ast_module);

    // 3. HIR lower
    let hir_module = match hir::lower(&ast_module) {
        Ok(h) => h,
        Err(e) => return (Stage::Hir, Some(format!("{e}"))),
    };

    // 4. MIR lower
    let mir_module = match mir::lower_to_mir(&hir_module) {
        Ok(m) => m,
        Err(e) => return (Stage::Mir, Some(format!("{e}"))),
    };

    // 5. C codegen
    let mut codegen = CCodegen::new();
    match codegen.compile_module(&mir_module) {
        Ok(_c_source) => (Stage::Done, None),
        Err(e) => (Stage::CCodegen, Some(format!("{e}"))),
    }
}

/// Run the pipeline on a dedicated thread with a large stack, catching panics.
fn run_pipeline_safe(source: String) -> (Stage, Option<String>) {
    let handle = std::thread::Builder::new()
        .name("pipeline-worker".into())
        .stack_size(PIPELINE_STACK_SIZE)
        .spawn(move || run_pipeline(&source))
        .expect("failed to spawn pipeline thread");

    match handle.join() {
        Ok(result) => result,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<String>() {
                format!("panic: {s}")
            } else if let Some(s) = panic_info.downcast_ref::<&str>() {
                format!("panic: {s}")
            } else {
                "panic: (unknown payload)".to_string()
            };
            // We don't know which stage panicked; report as Parse (earliest)
            // so it counts as failing all stages.
            (Stage::Parse, Some(msg))
        }
    }
}

// ---------------------------------------------------------------------------
// File collection
// ---------------------------------------------------------------------------

/// Recursively collect all `.spl` files under `dir`.
fn collect_spl_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_spl_recursive(dir, &mut files);
    files.sort();
    files
}

fn collect_spl_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_spl_recursive(&path, out);
        } else if path.extension().map_or(false, |ext| ext == "spl") {
            out.push(path);
        }
    }
}

// ---------------------------------------------------------------------------
// Reporting helpers
// ---------------------------------------------------------------------------

fn run_batch(files: &[PathBuf]) -> Vec<FileResult> {
    let mut results: Vec<FileResult> = Vec::new();

    for path in files {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                results.push(FileResult {
                    path: path.clone(),
                    reached: Stage::Parse,
                    error: Some(format!("read error: {e}")),
                });
                eprint!("!");
                continue;
            }
        };

        let (reached, error) = run_pipeline_safe(source);

        if error.is_none() {
            eprint!(".");
        } else {
            eprint!("x");
        }

        results.push(FileResult {
            path: path.clone(),
            reached,
            error,
        });
    }
    eprintln!(); // newline after progress dots
    results
}

fn print_summary(label: &str, results: &[FileResult]) {
    let total = results.len();
    let parse_pass = results.iter().filter(|r| r.passed(Stage::Parse)).count();
    let mono_pass = parse_pass; // monomorphize is infallible
    let hir_pass = results.iter().filter(|r| r.passed(Stage::Hir)).count();
    let mir_pass = results.iter().filter(|r| r.passed(Stage::Mir)).count();
    let c_pass = results.iter().filter(|r| r.passed(Stage::CCodegen)).count();

    eprintln!("\n=== Batch C Compile Results{} ===", label);
    eprintln!("Parse: {}/{}", parse_pass, total);
    eprintln!("Mono:  {}/{}", mono_pass, total);
    eprintln!("HIR:   {}/{}", hir_pass, total);
    eprintln!("MIR:   {}/{}", mir_pass, total);
    eprintln!("C:     {}/{}", c_pass, total);

    // Print per-file failures grouped by stage
    let failures: Vec<&FileResult> = results.iter().filter(|r| r.error.is_some()).collect();
    if !failures.is_empty() {
        eprintln!("\n=== Failures ({}) ===", failures.len());

        for stage in &[Stage::Parse, Stage::Hir, Stage::Mir, Stage::CCodegen] {
            let stage_failures: Vec<&&FileResult> = failures
                .iter()
                .filter(|r| r.reached == *stage)
                .collect();
            if stage_failures.is_empty() {
                continue;
            }
            eprintln!(
                "\n--- {} failures ({}) ---",
                stage.label(),
                stage_failures.len()
            );
            for f in &stage_failures {
                // Show path relative to the scanned dir for readability
                let rel = f.path.file_name().unwrap_or_default().to_string_lossy();
                let err = f.error.as_deref().unwrap_or("?");
                // Truncate very long errors
                let err_display = if err.len() > 200 {
                    format!("{}...", &err[..200])
                } else {
                    err.to_string()
                };
                eprintln!("  {}: {}", rel, err_display);
            }
        }
    }

    eprintln!();
}

fn project_root() -> PathBuf {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    crate_dir
        .parent() // src/temp_bootstrap/src
        .and_then(|p| p.parent()) // src/temp_bootstrap
        .and_then(|p| p.parent()) // src
        .and_then(|p| p.parent()) // project root
        .expect("could not find project root from CARGO_MANIFEST_DIR")
        .to_path_buf()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn batch_c_compile_00_common() {
    let compiler_dir = std::env::var("SRC_COMPILER_DIR").unwrap_or_else(|_| {
        project_root()
            .join("src/compiler/00.common")
            .to_string_lossy()
            .into_owned()
    });

    let dir = PathBuf::from(&compiler_dir);
    assert!(
        dir.is_dir(),
        "SRC_COMPILER_DIR does not exist or is not a directory: {}",
        dir.display()
    );

    let files = collect_spl_files(&dir);
    assert!(
        !files.is_empty(),
        "No .spl files found in {}",
        dir.display()
    );

    eprintln!(
        "\n=== Batch C Compile: {} files from {} ===\n",
        files.len(),
        dir.display()
    );

    let results = run_batch(&files);
    print_summary("", &results);

    let parse_pass = results.iter().filter(|r| r.passed(Stage::Parse)).count();
    assert!(
        parse_pass > 0,
        "No files parsed successfully - is SRC_COMPILER_DIR correct?"
    );
}

/// Same pipeline but scanning ALL compiler layers (00.common through 99.loader).
/// Gated behind SRC_COMPILER_DIR_ALL env var to avoid running by default.
#[test]
fn batch_c_compile_all_layers() {
    let compiler_dir = match std::env::var("SRC_COMPILER_DIR_ALL") {
        Ok(d) => d,
        Err(_) => {
            eprintln!("SRC_COMPILER_DIR_ALL not set, skipping batch_c_compile_all_layers");
            return;
        }
    };

    let dir = PathBuf::from(&compiler_dir);
    assert!(
        dir.is_dir(),
        "SRC_COMPILER_DIR_ALL does not exist or is not a directory: {}",
        dir.display()
    );

    let files = collect_spl_files(&dir);
    assert!(
        !files.is_empty(),
        "No .spl files found in {}",
        dir.display()
    );

    eprintln!(
        "\n=== Batch C Compile (ALL): {} files from {} ===\n",
        files.len(),
        dir.display()
    );

    let results = run_batch(&files);
    print_summary(" (ALL)", &results);

    let parse_pass = results.iter().filter(|r| r.passed(Stage::Parse)).count();
    assert!(
        parse_pass > 0,
        "No files parsed successfully - is SRC_COMPILER_DIR_ALL correct?"
    );
}
