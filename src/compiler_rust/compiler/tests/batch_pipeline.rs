//! Batch pipeline test for src/compiler/ .spl files through compiler_rust.
//!
//! Runs each .spl file through the pipeline stages:
//!   1. Parse  (simple_parser)
//!   2. Monomorphize  (monomorphize_module)
//!   3. HIR lower  (hir::lower)
//!   4. MIR lower  (mir::lower_to_mir)
//!   5. Codegen  (Cranelift AOT - optional, set BATCH_CODEGEN=1)
//!
//! Environment variables:
//! * `SRC_COMPILER_DIR` - directory to scan (default: src/compiler/)
//! * `BATCH_CODEGEN` - set to "1" to also run Cranelift codegen (slow)

use std::path::{Path, PathBuf};

use simple_compiler::codegen::Codegen;
use simple_compiler::hir::Lowerer;
use simple_compiler::module_resolver::ModuleResolver;
use simple_compiler::monomorphize::monomorphize_module;

/// Stack size for pipeline threads (16 MB).
const PIPELINE_STACK_SIZE: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Stage {
    Parse,
    Mono,
    Hir,
    Mir,
    Codegen,
    Done,
}

impl Stage {
    fn label(&self) -> &'static str {
        match self {
            Stage::Parse => "Parse",
            Stage::Mono => "Mono",
            Stage::Hir => "HIR",
            Stage::Mir => "MIR",
            Stage::Codegen => "Codegen",
            Stage::Done => "Done",
        }
    }
}

struct FileResult {
    path: PathBuf,
    reached: Stage,
    error: Option<String>,
}

impl FileResult {
    fn passed(&self, stage: Stage) -> bool {
        if self.error.is_none() {
            return true;
        }
        self.reached > stage
    }
}

fn run_pipeline(source: &str, file_path: &std::path::Path) -> (Stage, Option<String>) {
    // 1. Parse
    let mut parser = simple_parser::Parser::new(source);
    let ast_module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            let span_info = match &e {
                simple_parser::ParseError::UnexpectedToken { span, .. } => format!(" [L{}:{}]", span.line, span.column),
                simple_parser::ParseError::SyntaxError { line, column, .. } => format!(" [L{}:{}]", line, column),
                simple_parser::ParseError::MissingToken { span, .. } => format!(" [L{}:{}]", span.line, span.column),
                simple_parser::ParseError::InvalidPattern { span, .. } => format!(" [L{}:{}]", span.line, span.column),
                simple_parser::ParseError::ContextualSyntaxError { span, .. } => {
                    format!(" [L{}:{}]", span.line, span.column)
                }
                _ => String::new(),
            };
            return (Stage::Parse, Some(format!("{e}{span_info}")));
        }
    };

    // 2. Monomorphize (infallible)
    let ast_module = monomorphize_module(&ast_module);

    // 3. HIR lower (lenient with project-level module resolver)
    let root = project_root();
    let source_root = root.join("src");
    let module_resolver = ModuleResolver::new(root.clone(), source_root);
    let mut lowerer = Lowerer::with_module_resolver(module_resolver, file_path.to_path_buf());
    lowerer.set_strict_mode(false); // lenient memory mode
    lowerer.set_lenient_types(true); // unknown types → ANY instead of error
    let hir_module = match lowerer.lower_module(&ast_module) {
        Ok(h) => h,
        Err(e) => return (Stage::Hir, Some(format!("{e}"))),
    };

    // 4. MIR lower
    let mir_module = match simple_compiler::mir::lower_to_mir(&hir_module) {
        Ok(m) => m,
        Err(e) => return (Stage::Mir, Some(format!("{e}"))),
    };

    // 5. Codegen (Cranelift AOT) - only if BATCH_CODEGEN=1
    //    Creating a Codegen per file is slow (~300ms each), so this is opt-in.
    if std::env::var("BATCH_CODEGEN").map_or(false, |v| v == "1") {
        match Codegen::new() {
            Ok(codegen) => match codegen.compile_module(&mir_module) {
                Ok(_object_code) => (Stage::Done, None),
                Err(e) => (Stage::Codegen, Some(format!("{e}"))),
            },
            Err(e) => (Stage::Codegen, Some(format!("codegen init: {e}"))),
        }
    } else {
        (Stage::Done, None)
    }
}

fn run_pipeline_safe(source: String, file_path: PathBuf) -> (Stage, Option<String>) {
    let handle = std::thread::Builder::new()
        .name("pipeline-worker".into())
        .stack_size(PIPELINE_STACK_SIZE)
        .spawn(move || run_pipeline(&source, &file_path))
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
            (Stage::Parse, Some(msg))
        }
    }
}

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

fn project_root() -> PathBuf {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // compiler_rust/compiler -> compiler_rust -> src -> project root
    crate_dir
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .expect("could not find project root")
        .to_path_buf()
}

fn run_batch(files: &[PathBuf]) -> Vec<FileResult> {
    let mut results = Vec::new();

    for (i, path) in files.iter().enumerate() {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                results.push(FileResult {
                    path: path.clone(),
                    reached: Stage::Parse,
                    error: Some(format!("read error: {e}")),
                });
                continue;
            }
        };

        let (reached, error) = run_pipeline_safe(source, path.clone());

        if (i + 1) % 100 == 0 {
            eprintln!("  [{}/{}]", i + 1, files.len());
        }

        results.push(FileResult {
            path: path.clone(),
            reached,
            error,
        });
    }
    results
}

fn print_summary(label: &str, results: &[FileResult]) {
    let total = results.len();
    let parse_pass = results.iter().filter(|r| r.passed(Stage::Parse)).count();
    let mono_pass = parse_pass;
    let hir_pass = results.iter().filter(|r| r.passed(Stage::Hir)).count();
    let mir_pass = results.iter().filter(|r| r.passed(Stage::Mir)).count();
    let codegen_pass = results.iter().filter(|r| r.passed(Stage::Codegen)).count();
    let all_pass = results.iter().filter(|r| r.error.is_none()).count();

    eprintln!("\n=== Batch Pipeline Results{} ===", label);
    eprintln!("Total files: {}", total);
    eprintln!("Parse:   {}/{}", parse_pass, total);
    eprintln!("Mono:    {}/{}", mono_pass, total);
    eprintln!("HIR:     {}/{}", hir_pass, total);
    eprintln!("MIR:     {}/{}", mir_pass, total);
    eprintln!("Codegen: {}/{}", codegen_pass, total);
    eprintln!("All:     {}/{}", all_pass, total);

    // Print failures grouped by stage
    let failures: Vec<&FileResult> = results.iter().filter(|r| r.error.is_some()).collect();
    if !failures.is_empty() {
        for stage in &[Stage::Parse, Stage::Hir, Stage::Mir, Stage::Codegen] {
            let stage_failures: Vec<&&FileResult> = failures.iter().filter(|r| r.reached == *stage).collect();
            if stage_failures.is_empty() {
                continue;
            }
            eprintln!("\n--- {} failures ({}) ---", stage.label(), stage_failures.len());
            for f in stage_failures.iter().take(200) {
                let rel = f.path.strip_prefix(project_root()).unwrap_or(&f.path);
                let err = f.error.as_deref().unwrap_or("?");
                let err_short = if err.len() > 250 {
                    format!("{}...", &err[..250])
                } else {
                    err.to_string()
                };
                eprintln!("  {}: {}", rel.display(), err_short);
            }
            if stage_failures.len() > 300 {
                eprintln!("  ... and {} more", stage_failures.len() - 300);
            }
        }
    }
    eprintln!();
}

#[test]
fn batch_pipeline_all() {
    let compiler_dir = std::env::var("SRC_COMPILER_DIR")
        .unwrap_or_else(|_| project_root().join("src/compiler").to_string_lossy().into_owned());

    let dir = PathBuf::from(&compiler_dir);
    assert!(dir.is_dir(), "directory not found: {}", dir.display());

    let files = collect_spl_files(&dir);
    assert!(!files.is_empty(), "No .spl files found in {}", dir.display());

    eprintln!("\n=== Batch Pipeline: {} files from {} ===", files.len(), dir.display());

    let results = run_batch(&files);
    print_summary("", &results);

    let parse_pass = results.iter().filter(|r| r.passed(Stage::Parse)).count();
    eprintln!(
        "Parse pass rate: {:.1}%",
        100.0 * parse_pass as f64 / files.len() as f64
    );
}
