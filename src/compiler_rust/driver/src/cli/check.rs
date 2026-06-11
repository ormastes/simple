//! Syntax and type checking without execution.
//!
//! The `simple check` command validates Simple source code by:
//! - Parsing source code and reporting syntax errors
//! - Validating import statements (module resolution)
//! - Checking type correctness (basic validation)
//! - Supporting multiple files and glob patterns
//! - Providing human-readable or JSON output

use serde::{Deserialize, Serialize};
use simple_common::target::Target;
use simple_compiler::module_resolver::ModuleResolver;
use simple_compiler::short_grammar::collect_short_grammar_suggestions;
use simple_compiler::{LintChecker, LintConfig, LintLevel, LintName};
use simple_parser::ast::{Block, Expr, ImportTarget, ModulePath, Node, Pattern, Type};
use simple_parser::{NumericSuffix, Parser, ParseError};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

/// Check options
#[derive(Debug, Clone, Default)]
pub struct CheckOptions {
    /// Output JSON format for tooling
    pub json: bool,
    /// Verbose output (show additional details)
    pub verbose: bool,
    /// Quiet mode (only show errors, no progress)
    pub quiet: bool,
    /// Additional source roots for module resolution
    pub source_roots: Vec<PathBuf>,
    /// Promote runtime-family boundary crossings to hard errors.
    pub deny_gc_boundary_crossings: bool,
    /// Optional target preset for target-restricted checks.
    pub target: Option<Target>,
}

/// Check result for a single file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileCheckResult {
    pub file: String,
    pub status: CheckStatus,
    pub errors: Vec<CheckError>,
}

/// Check status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CheckStatus {
    Success,
    Warning,
    Error,
}

/// Check error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckError {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub severity: ErrorSeverity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub found: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub help: Vec<String>,
}

/// Error severity
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ErrorSeverity {
    Error,
    Warning,
}

/// Overall check result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    pub status: CheckStatus,
    pub files_checked: usize,
    pub errors: Vec<CheckError>,
}

/// Run check command on multiple files
pub fn run_check(files: &[PathBuf], options: CheckOptions) -> i32 {
    let files = expand_check_inputs(files);
    let mut all_results = Vec::new();
    let mut has_errors = false;
    let deny_gc_boundary_crossings = should_deny_gc_boundary_crossings(&options);

    for file in &files {
        if !options.quiet && options.verbose {
            println!("Checking {}...", file.display());
        }

        let result = check_file(file, &options.source_roots, deny_gc_boundary_crossings);

        match &result.status {
            CheckStatus::Success => {
                if !options.quiet && !options.json {
                    println!("Checking {}... \x1b[32mOK\x1b[0m", file.display());
                }
            }
            CheckStatus::Warning | CheckStatus::Error => {
                if result.errors.iter().any(|error| error.severity == ErrorSeverity::Error) {
                    has_errors = true;
                }
                if !options.json {
                    for error in &result.errors {
                        print_error(error);
                    }
                }
            }
        }

        all_results.push(result);
    }

    // Output results
    if options.json {
        output_json(&all_results);
    } else if !options.quiet {
        println!();
        let error_count: usize = all_results
            .iter()
            .map(|r| r.errors.iter().filter(|e| e.severity == ErrorSeverity::Error).count())
            .sum();
        let warning_count: usize = all_results
            .iter()
            .map(|r| r.errors.iter().filter(|e| e.severity == ErrorSeverity::Warning).count())
            .sum();
        if error_count > 0 {
            println!(
                "\x1b[31m✗ {} error(s) found in {} file(s)\x1b[0m",
                error_count,
                files.len()
            );
        } else if warning_count > 0 {
            println!(
                "\x1b[33m⚠ {} warning(s) found in {} file(s)\x1b[0m",
                warning_count,
                files.len()
            );
        } else {
            println!("\x1b[32m✓ All checks passed ({} file(s))\x1b[0m", files.len());
        }
    }

    if has_errors {
        1
    } else {
        0
    }
}

fn should_deny_gc_boundary_crossings(options: &CheckOptions) -> bool {
    options.deny_gc_boundary_crossings || options.target.is_some_and(|target| target.is_baremetal())
}

fn expand_check_inputs(inputs: &[PathBuf]) -> Vec<PathBuf> {
    let mut expanded = Vec::new();
    for input in inputs {
        expand_check_input(input, &mut expanded);
    }
    expanded.sort();
    expanded.dedup();
    expanded
}

fn expand_check_input(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let mut entries = match fs::read_dir(path) {
            Ok(entries) => entries.filter_map(Result::ok).map(|e| e.path()).collect::<Vec<_>>(),
            Err(_) => {
                return;
            }
        };
        entries.sort();
        for entry in entries {
            expand_check_input(&entry, out);
        }
        return;
    }

    if path.extension().and_then(|ext| ext.to_str()) == Some("spl") {
        out.push(path.to_path_buf());
    }
}

/// Check a single file
fn check_file(path: &Path, source_roots: &[PathBuf], deny_gc_boundary_crossings: bool) -> FileCheckResult {
    // Read file
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return FileCheckResult {
                file: path.display().to_string(),
                status: CheckStatus::Error,
                errors: vec![CheckError {
                    file: path.display().to_string(),
                    line: 0,
                    column: 0,
                    severity: ErrorSeverity::Error,
                    code: Some("E0001".to_string()),
                    message: format!("cannot read file: {}", e),
                    expected: None,
                    found: None,
                    notes: Vec::new(),
                    help: vec!["check that the path exists and is readable".to_string()],
                }],
            };
        }
    };

    let mut errors = Vec::new();

    // Parse source
    let mut parser = Parser::new(&source);
    match parser.parse() {
        Ok(module) => {
            // Parsing succeeded, validate imports
            validate_imports(path, &module.items, &mut errors, source_roots);
            validate_gc_boundary_lints(path, &module.items, &mut errors, deny_gc_boundary_crossings);
            validate_noalloc_reachable_import_closure(path, &mut errors, source_roots, deny_gc_boundary_crossings);
            validate_basic_type_annotations(path, &module.items, &mut errors);
            validate_concurrency_api_calls(path, &module.items, &mut errors);
            validate_numbered_concurrency_source(path, &source, &mut errors);
            validate_short_grammar_suggestions(path, &source, &mut errors);
        }
        Err(e) => {
            // Convert ParseError to CheckError
            errors.push(parse_error_to_check_error(&e, path));
        }
    }

    let has_hard_errors = errors.iter().any(|error| error.severity == ErrorSeverity::Error);
    let status = if has_hard_errors {
        CheckStatus::Error
    } else if !errors.is_empty() {
        CheckStatus::Warning
    } else {
        CheckStatus::Success
    };

    FileCheckResult {
        file: path.display().to_string(),
        status,
        errors,
    }
}

fn validate_numbered_concurrency_source(file_path: &Path, source: &str, errors: &mut Vec<CheckError>) {
    let allow_runtime_pool_externs = file_path.ends_with("src/lib/nogc_async_mut/concurrent/multicore_green.spl")
        || file_path.ends_with("src/lib/gc_async_mut/concurrent/multicore_green.spl")
        || file_path.ends_with("src/lib/nogc_sync_mut/concurrent/multicore_green.spl")
        || file_path.ends_with("src/lib/gc_sync_mut/concurrent/multicore_green.spl");
    for (line_index, line) in source.lines().enumerate() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("extern fn ") {
            continue;
        }
        for (name, replacement) in [
            ("rt_thread_spawn_isolated2", "rt_thread_spawn_isolated_with_args"),
            ("rt_thread_spawn_limited2", "rt_thread_spawn_limited_with_args"),
            ("thread_spawn2", "thread_spawn_with_args"),
            ("spawn_isolated2", "spawn_isolated_with_args"),
            ("spawn_limited2", "spawn_limited_with_args"),
        ] {
            if let Some(offset) = line.find(name) {
                errors.push(numbered_concurrency_error(
                    file_path,
                    line_index + 1,
                    offset + 1,
                    name,
                    replacement,
                ));
            }
        }
        if !allow_runtime_pool_externs {
            for name in [
                "rt_pool_submit",
                "rt_pool_join",
                "rt_pool_is_done",
                "rt_pool_set_parallelism",
                "rt_pool_get_parallelism",
            ] {
                if let Some(offset) = line.find(name) {
                    errors.push(internal_concurrency_runtime_error(
                        file_path,
                        line_index + 1,
                        offset + 1,
                        name,
                    ));
                }
            }
        }
    }
}

fn validate_short_grammar_suggestions(file_path: &Path, source: &str, errors: &mut Vec<CheckError>) {
    for suggestion in collect_short_grammar_suggestions(source) {
        errors.push(CheckError {
            file: file_path.display().to_string(),
            line: suggestion.line,
            column: suggestion.column,
            severity: ErrorSeverity::Warning,
            code: Some("L-STYLE-001".to_string()),
            message: "readable callback can use short grammar".to_string(),
            expected: None,
            found: None,
            notes: Vec::new(),
            help: vec![format!("replace with `{}`", suggestion.replacement)],
        });
    }
}

fn validate_gc_boundary_lints(
    file_path: &Path,
    items: &[Node],
    errors: &mut Vec<CheckError>,
    deny_gc_boundary_crossings: bool,
) {
    let mut config = LintConfig::new();
    for lint in LintName::all_lints() {
        config.set_level(lint, LintLevel::Allow);
    }
    let gc_boundary_level = if deny_gc_boundary_crossings {
        LintLevel::Deny
    } else {
        LintLevel::Warn
    };
    config.set_level(LintName::GcBoundaryCrossing, gc_boundary_level);

    let mut checker = LintChecker::with_config(config).with_source_file(Some(file_path.to_path_buf()));
    checker.check_module(items);

    for diagnostic in checker.take_diagnostics() {
        if diagnostic.lint != LintName::GcBoundaryCrossing {
            continue;
        }

        let mut help = Vec::new();
        if let Some(suggestion) = &diagnostic.suggestion {
            help.push(suggestion.clone());
        }

        errors.push(CheckError {
            file: file_path.display().to_string(),
            line: diagnostic.span.line,
            column: diagnostic.span.column,
            severity: if diagnostic.is_error() {
                ErrorSeverity::Error
            } else {
                ErrorSeverity::Warning
            },
            code: Some(diagnostic.lint.as_str().to_string()),
            message: diagnostic.message,
            expected: None,
            found: None,
            notes: Vec::new(),
            help,
        });
    }
}

#[derive(Debug, Clone)]
struct NoallocRoots {
    noalloc: PathBuf,
    common: PathBuf,
}

#[derive(Debug)]
struct ImportEdge {
    line: usize,
    column: usize,
    module: String,
    path: ModulePath,
    target: ImportTarget,
}

const NOALLOC_FAMILY: &str = "nogc_async_mut_noalloc";

fn validate_noalloc_reachable_import_closure(
    file_path: &Path,
    errors: &mut Vec<CheckError>,
    source_roots: &[PathBuf],
    deny_gc_boundary_crossings: bool,
) {
    if !deny_gc_boundary_crossings {
        return;
    }

    let abs_path = absolute_path(file_path);
    let Some(roots) = noalloc_roots_for_file(&abs_path, source_roots) else {
        return;
    };

    let mut queue = vec![abs_path];
    let mut seen = HashSet::new();

    while let Some(path) = queue.pop() {
        let path = absolute_path(&path);
        if !seen.insert(path.clone()) {
            continue;
        }

        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(_) => continue,
        };

        validate_noalloc_source_text(&path, &source, errors);

        let mut parser = Parser::new(&source);
        let Ok(module) = parser.parse() else {
            continue;
        };

        for import in noalloc_import_edges(&module.items) {
            if is_forbidden_noalloc_module(&import.module) {
                push_noalloc_check_error(
                    errors,
                    &path,
                    import.line,
                    import.column,
                    format!(
                        "noalloc reachable import '{}' crosses into an allocating or host runtime family",
                        import.module
                    ),
                    vec!["keep noalloc closures within std.nogc_async_mut_noalloc and std.common".to_string()],
                );
                continue;
            }

            let Some(resolved) = resolve_noalloc_import(&roots, &path, &import.path, &import.target) else {
                continue;
            };

            if !is_path_within(&resolved, &roots.noalloc) && !is_path_within(&resolved, &roots.common) {
                push_noalloc_check_error(
                    errors,
                    &path,
                    import.line,
                    import.column,
                    format!(
                        "noalloc reachable import '{}' resolves outside the allowed noalloc/common roots",
                        import.module
                    ),
                    vec![format!("resolved path: {}", resolved.display())],
                );
                continue;
            }

            if !seen.contains(&resolved) {
                queue.push(resolved);
            }
        }
    }
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    }
}

fn noalloc_roots_for_file(file_path: &Path, source_roots: &[PathBuf]) -> Option<NoallocRoots> {
    for lib_root in candidate_lib_roots(file_path, source_roots) {
        let noalloc = lib_root.join(NOALLOC_FAMILY);
        if is_path_within(file_path, &noalloc) {
            return Some(NoallocRoots {
                noalloc,
                common: lib_root.join("common"),
            });
        }
    }

    None
}

fn candidate_lib_roots(file_path: &Path, source_roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    for source_root in source_roots {
        roots.push(if source_root.is_absolute() {
            source_root.clone()
        } else {
            cwd.join(source_root)
        });
    }

    if let Some(lib_root) = lib_root_from_path(file_path) {
        roots.push(lib_root);
    }

    if let Some(workspace_root) = find_simple_workspace_root(file_path) {
        roots.push(workspace_root.join("src/lib"));
    }

    roots.sort();
    roots.dedup();
    roots
}

fn lib_root_from_path(file_path: &Path) -> Option<PathBuf> {
    let components = file_path.components().collect::<Vec<_>>();
    for index in 0..components.len().saturating_sub(2) {
        if components[index].as_os_str() == "src"
            && components[index + 1].as_os_str() == "lib"
            && components[index + 2].as_os_str() == NOALLOC_FAMILY
        {
            let mut root = PathBuf::new();
            for component in &components[..index + 2] {
                root.push(component.as_os_str());
            }
            return Some(root);
        }
    }

    None
}

fn validate_noalloc_source_text(file_path: &Path, source: &str, errors: &mut Vec<CheckError>) {
    for (line_index, line) in source.lines().enumerate() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("@alloc") || trimmed.starts_with("# @alloc") || trimmed.starts_with("#@alloc") {
            push_noalloc_check_error(
                errors,
                file_path,
                line_index + 1,
                line.len() - trimmed.len() + 1,
                "allocation annotation is reachable from a noalloc closure".to_string(),
                vec!["move allocating APIs to a GC/runtime-family facade outside the noalloc backend".to_string()],
            );
        }

        if line.contains("malloc(") || line.contains("calloc(") || line.contains("free(") || line.contains("rt_alloc") {
            push_noalloc_check_error(
                errors,
                file_path,
                line_index + 1,
                1,
                "host allocation API is reachable from a noalloc closure".to_string(),
                vec!["noalloc backend code must use caller-provided storage or explicit backend handles".to_string()],
            );
        }
    }
}

fn noalloc_import_edges(items: &[Node]) -> Vec<ImportEdge> {
    let mut edges = Vec::new();
    for item in items {
        match item {
            Node::UseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            Node::CommonUseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            Node::ExportUseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            _ => {}
        }
    }
    edges
}

fn display_import_module(module_path: &ModulePath, target: &ImportTarget) -> String {
    target_module_path(module_path, target)
        .unwrap_or_else(|| module_path.clone())
        .segments
        .join(".")
}

fn is_forbidden_noalloc_module(module: &str) -> bool {
    [
        "std.nogc_sync_mut.",
        "std.nogc_async_mut.",
        "std.nogc_async_immut.",
        "std.gc_async_mut.",
        "std.posix.",
        "std.linux.",
        "posix.",
        "linux.",
        "os.",
        "app.",
        "examples.",
    ]
    .iter()
    .any(|prefix| module.starts_with(prefix))
}

fn resolve_noalloc_import(
    roots: &NoallocRoots,
    current_file: &Path,
    module_path: &ModulePath,
    target: &ImportTarget,
) -> Option<PathBuf> {
    let mut candidates = Vec::new();
    candidates.extend(noalloc_module_candidates(roots, &module_path.segments, current_file));

    if let Some(target_path) = target_module_path(module_path, target) {
        candidates.extend(noalloc_module_candidates(roots, &target_path.segments, current_file));
    }

    candidates.into_iter().find_map(existing_noalloc_candidate)
}

fn target_module_path(module_path: &ModulePath, target: &ImportTarget) -> Option<ModulePath> {
    match target {
        ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
            let mut segments = module_path.segments.clone();
            segments.push(name.clone());
            Some(ModulePath::new(segments))
        }
        _ => None,
    }
}

fn noalloc_module_candidates(roots: &NoallocRoots, segments: &[String], current_file: &Path) -> Vec<PathBuf> {
    if segments.is_empty() {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    let first = segments[0].as_str();
    let second = segments.get(1).map(String::as_str);

    if first == "std" || first == "lib" {
        match second {
            Some(NOALLOC_FAMILY) => candidates.push(roots.noalloc.join(PathBuf::from_iter(&segments[2..]))),
            Some("common") => candidates.push(roots.common.join(PathBuf::from_iter(&segments[2..]))),
            Some(_) if first == "std" => {
                candidates.push(roots.noalloc.join(PathBuf::from_iter(&segments[1..])));
                candidates.push(roots.common.join(PathBuf::from_iter(&segments[1..])));
            }
            _ => {}
        }
    } else if first == "common" {
        candidates.push(roots.common.join(PathBuf::from_iter(&segments[1..])));
    } else {
        candidates.push(
            current_file
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(PathBuf::from_iter(segments)),
        );
    }

    candidates
}

fn existing_noalloc_candidate(path: PathBuf) -> Option<PathBuf> {
    let file = path.with_extension("spl");
    if file.is_file() {
        return Some(file);
    }

    let init = path.join("__init__.spl");
    if init.is_file() {
        return Some(init);
    }

    None
}

fn is_path_within(path: &Path, root: &Path) -> bool {
    let path = absolute_path(path);
    let root = absolute_path(root);
    path.starts_with(root)
}

fn push_noalloc_check_error(
    errors: &mut Vec<CheckError>,
    file_path: &Path,
    line: usize,
    column: usize,
    message: String,
    help: Vec<String>,
) {
    let file = file_path.display().to_string();
    if errors.iter().any(|error| {
        error.code.as_deref() == Some("E0413")
            && error.file == file
            && error.line == line
            && error.column == column
            && error.message == message
    }) {
        return;
    }

    errors.push(noalloc_check_error(file_path, line, column, message, help));
}

fn noalloc_check_error(file_path: &Path, line: usize, column: usize, message: String, help: Vec<String>) -> CheckError {
    CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E0413".to_string()),
        message,
        expected: Some("nogc_async_mut_noalloc/common reachable imports only".to_string()),
        found: None,
        notes: Vec::new(),
        help,
    }
}

fn validate_basic_type_annotations(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>) {
    for item in items {
        validate_basic_type_annotation_node(file_path, item, None, errors);
    }
}

fn validate_concurrency_api_calls(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>) {
    let imported = imported_concurrency_call_bindings(items);
    if imported.is_empty() {
        return;
    }

    for item in items {
        validate_concurrency_api_node(file_path, item, &imported, errors);
    }
}

fn imported_concurrency_call_bindings(items: &[Node]) -> HashMap<String, String> {
    let mut imported = HashMap::new();
    for item in items {
        match item {
            Node::UseStmt(stmt) => collect_concurrency_import_targets(&stmt.path, &stmt.target, &mut imported),
            Node::CommonUseStmt(stmt) => collect_concurrency_import_targets(&stmt.path, &stmt.target, &mut imported),
            Node::ExportUseStmt(stmt) => collect_concurrency_import_targets(&stmt.path, &stmt.target, &mut imported),
            Node::MultiUse(stmt) => {
                for (path, target) in &stmt.imports {
                    collect_concurrency_import_targets(path, target, &mut imported);
                }
            }
            _ => {}
        }
    }
    imported
}

fn collect_concurrency_import_targets(
    path: &simple_parser::ast::ModulePath,
    target: &ImportTarget,
    imported: &mut HashMap<String, String>,
) {
    let owner_path = path.segments.join(".");
    collect_concurrency_import_target(&owner_path, target, imported);
}

fn collect_concurrency_import_target(owner_path: &str, target: &ImportTarget, imported: &mut HashMap<String, String>) {
    match target {
        ImportTarget::Single(name) => {
            if concurrency_call_rule(name).is_some() && concurrency_wrong_surface_error_owner_accepts(owner_path, name)
            {
                imported.insert(name.clone(), name.clone());
            }
        }
        ImportTarget::Aliased { name, alias } => {
            if concurrency_call_rule(name).is_some() && concurrency_wrong_surface_error_owner_accepts(owner_path, name)
            {
                imported.insert(alias.clone(), name.clone());
            }
        }
        ImportTarget::Group(targets) => {
            for target in targets {
                collect_concurrency_import_target(owner_path, target, imported);
            }
        }
        ImportTarget::Glob => {}
    }
}

fn concurrency_wrong_surface_error_owner_accepts(owner_path: &str, name: &str) -> bool {
    match name {
        "thread_spawn" | "thread_spawn_with_args" => is_concurrency_thread_path(owner_path),
        "green_spawn" => is_green_thread_path(owner_path) || is_cooperative_green_path(owner_path),
        "cooperative_green_spawn" | "cooperative_green_spawn_value" => is_cooperative_green_path(owner_path),
        "multicore_green_spawn" | "multicore_green_set_parallelism" => is_multicore_green_path(owner_path),
        _ => false,
    }
}

fn validate_concurrency_api_node(
    file_path: &Path,
    item: &Node,
    imported: &HashMap<String, String>,
    errors: &mut Vec<CheckError>,
) {
    match item {
        Node::Function(function) => validate_concurrency_api_block(file_path, &function.body, imported, errors),
        Node::Let(stmt) => {
            if let Some(value) = &stmt.value {
                validate_concurrency_api_expr(file_path, value, imported, errors);
            }
        }
        Node::Const(stmt) => validate_concurrency_api_expr(file_path, &stmt.value, imported, errors),
        Node::Static(stmt) => validate_concurrency_api_expr(file_path, &stmt.value, imported, errors),
        Node::Assignment(stmt) => {
            validate_concurrency_api_expr(file_path, &stmt.target, imported, errors);
            validate_concurrency_api_expr(file_path, &stmt.value, imported, errors);
        }
        Node::Return(stmt) => {
            if let Some(value) = &stmt.value {
                validate_concurrency_api_expr(file_path, value, imported, errors);
            }
        }
        Node::Expression(expr) => validate_concurrency_api_expr(file_path, expr, imported, errors),
        Node::If(stmt) => {
            validate_concurrency_api_expr(file_path, &stmt.condition, imported, errors);
            validate_concurrency_api_block(file_path, &stmt.then_block, imported, errors);
            for (_, condition, block) in &stmt.elif_branches {
                validate_concurrency_api_expr(file_path, condition, imported, errors);
                validate_concurrency_api_block(file_path, block, imported, errors);
            }
            if let Some(block) = &stmt.else_block {
                validate_concurrency_api_block(file_path, block, imported, errors);
            }
        }
        Node::For(stmt) => {
            validate_concurrency_api_expr(file_path, &stmt.iterable, imported, errors);
            validate_concurrency_api_block(file_path, &stmt.body, imported, errors);
        }
        Node::While(stmt) => {
            validate_concurrency_api_expr(file_path, &stmt.condition, imported, errors);
            validate_concurrency_api_block(file_path, &stmt.body, imported, errors);
        }
        Node::Loop(stmt) => validate_concurrency_api_block(file_path, &stmt.body, imported, errors),
        Node::Skip(stmt) => {
            if let simple_parser::ast::SkipBody::Block(block) = &stmt.body {
                validate_concurrency_api_block(file_path, block, imported, errors);
            }
        }
        _ => {}
    }
}

fn validate_concurrency_api_block(
    file_path: &Path,
    block: &Block,
    imported: &HashMap<String, String>,
    errors: &mut Vec<CheckError>,
) {
    for statement in &block.statements {
        validate_concurrency_api_node(file_path, statement, imported, errors);
    }
}

fn validate_concurrency_api_expr(
    file_path: &Path,
    expr: &Expr,
    imported: &HashMap<String, String>,
    errors: &mut Vec<CheckError>,
) {
    match expr {
        Expr::Call { callee, args } => {
            if let Some(canonical_name) = concurrency_call_canonical_name(callee, imported) {
                validate_concurrency_call_shape(file_path, canonical_name, args, errors);
            }
            validate_concurrency_api_expr(file_path, callee, imported, errors);
            for arg in args {
                validate_concurrency_api_expr(file_path, &arg.value, imported, errors);
            }
        }
        Expr::MethodCall { receiver, args, .. }
        | Expr::FunctionalUpdate {
            target: receiver, args, ..
        } => {
            validate_concurrency_api_expr(file_path, receiver, imported, errors);
            for arg in args {
                validate_concurrency_api_expr(file_path, &arg.value, imported, errors);
            }
        }
        Expr::Binary { left, right, .. } => {
            validate_concurrency_api_expr(file_path, left, imported, errors);
            validate_concurrency_api_expr(file_path, right, imported, errors);
        }
        Expr::Unary { operand, .. }
        | Expr::Await(operand)
        | Expr::Yield(Some(operand))
        | Expr::New { expr: operand, .. }
        | Expr::Cast { expr: operand, .. }
        | Expr::Spread(operand)
        | Expr::DictSpread(operand)
        | Expr::Try(operand)
        | Expr::ForceUnwrap(operand)
        | Expr::ExistsCheck(operand)
        | Expr::UnwrapOrReturn(operand)
        | Expr::CastOrReturn { expr: operand, .. }
        | Expr::ContractOld(operand) => validate_concurrency_api_expr(file_path, operand, imported, errors),
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            validate_concurrency_api_expr(file_path, condition, imported, errors);
            validate_concurrency_api_expr(file_path, then_branch, imported, errors);
            if let Some(else_branch) = else_branch {
                validate_concurrency_api_expr(file_path, else_branch, imported, errors);
            }
        }
        Expr::Tuple(values) | Expr::Array(values) | Expr::VecLiteral(values) => {
            for value in values {
                validate_concurrency_api_expr(file_path, value, imported, errors);
            }
        }
        Expr::DoBlock(nodes) => {
            for node in nodes {
                validate_concurrency_api_node(file_path, node, imported, errors);
            }
        }
        _ => {}
    }
}

fn concurrency_call_canonical_name<'a>(callee: &'a Expr, imported: &'a HashMap<String, String>) -> Option<&'a str> {
    match callee {
        Expr::Identifier(name) => imported.get(name).map(String::as_str),
        Expr::Path(segments) => segments
            .last()
            .and_then(|name| concurrency_call_rule(name).map(|_| name.as_str())),
        _ => None,
    }
}

fn validate_concurrency_call_shape(
    file_path: &Path,
    canonical_name: &str,
    args: &[simple_parser::ast::Argument],
    errors: &mut Vec<CheckError>,
) {
    let Some(rule) = concurrency_call_rule(canonical_name) else {
        return;
    };
    if args.len() != rule.expected_arity {
        errors.push(concurrency_call_shape_error(
            file_path,
            args.first().map(|arg| arg.span.line).unwrap_or(1),
            args.first().map(|arg| arg.span.column).unwrap_or(1),
            canonical_name,
            rule.expected,
            format!("{} argument(s)", args.len()),
            rule.help,
        ));
        return;
    }

    let Some(first) = args.first() else {
        return;
    };
    let accepted = match rule.first_arg {
        ConcurrencyFirstArg::Closure => matches!(first.value, Expr::Lambda { .. }),
        ConcurrencyFirstArg::Integer => {
            literal_type_name(&first.value).is_some_and(|found| numeric_literal_type_compatible("i64", found))
        }
    };
    if !accepted {
        errors.push(concurrency_call_shape_error(
            file_path,
            first.span.line,
            first.span.column,
            canonical_name,
            rule.expected,
            concurrency_arg_found(&first.value),
            rule.help,
        ));
    }
}

#[derive(Debug, Clone, Copy)]
enum ConcurrencyFirstArg {
    Closure,
    Integer,
}

#[derive(Debug, Clone, Copy)]
struct ConcurrencyCallRule {
    expected_arity: usize,
    first_arg: ConcurrencyFirstArg,
    expected: &'static str,
    help: &'static str,
}

fn concurrency_call_rule(name: &str) -> Option<ConcurrencyCallRule> {
    match name {
        "thread_spawn" | "green_spawn" | "cooperative_green_spawn" | "multicore_green_spawn" => Some(ConcurrencyCallRule {
            expected_arity: 1,
            first_arg: ConcurrencyFirstArg::Closure,
            expected: "single zero-argument value closure",
            help: "pass a closure such as `\\: 1`; use thread_spawn_with_args for explicit thread arguments",
        }),
        "multicore_green_set_parallelism" => Some(ConcurrencyCallRule {
            expected_arity: 1,
            first_arg: ConcurrencyFirstArg::Integer,
            expected: "single integer worker count",
            help: "pass an integer worker count such as `4`, not text",
        }),
        _ => None,
    }
}

fn concurrency_arg_found(expr: &Expr) -> String {
    match expr {
        Expr::Lambda { .. } => "closure".to_string(),
        _ => literal_type_name(expr)
            .map(|found| found.display_name().to_string())
            .unwrap_or_else(|| "non-literal expression".to_string()),
    }
}

fn concurrency_call_shape_error(
    file_path: &Path,
    line: usize,
    column: usize,
    name: &str,
    expected: &str,
    found: String,
    help: &str,
) -> CheckError {
    CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E-PAR-004".to_string()),
        message: format!("{name} was called with an invalid concurrency API argument"),
        expected: Some(expected.to_string()),
        found: Some(found),
        notes: vec![
            "public concurrency surfaces fail closed so OS-thread, cooperative-green, and multicore-green behavior cannot be confused"
                .to_string(),
        ],
        help: vec![help.to_string()],
    }
}

fn validate_basic_type_annotation_node(
    file_path: &Path,
    item: &Node,
    return_type: Option<&Type>,
    errors: &mut Vec<CheckError>,
) {
    match item {
        Node::Function(function) => {
            validate_basic_type_annotation_block(file_path, &function.body, function.return_type.as_ref(), errors);
        }
        Node::Let(stmt) => {
            if let (Some(expected), Some(value)) = (declared_type(&stmt.ty, &stmt.pattern), stmt.value.as_ref()) {
                validate_literal_type(file_path, stmt.span.line, stmt.span.column, expected, value, errors);
            }
        }
        Node::Const(stmt) => {
            if let Some(expected) = stmt.ty.as_ref() {
                validate_literal_type(
                    file_path,
                    stmt.span.line,
                    stmt.span.column,
                    expected,
                    &stmt.value,
                    errors,
                );
            }
        }
        Node::Static(stmt) => {
            if let Some(expected) = stmt.ty.as_ref() {
                validate_literal_type(
                    file_path,
                    stmt.span.line,
                    stmt.span.column,
                    expected,
                    &stmt.value,
                    errors,
                );
            }
        }
        Node::Return(stmt) => {
            if let (Some(expected), Some(value)) = (return_type, stmt.value.as_ref()) {
                validate_literal_type(file_path, stmt.span.line, stmt.span.column, expected, value, errors);
            }
        }
        Node::If(stmt) => {
            validate_basic_type_annotation_block(file_path, &stmt.then_block, return_type, errors);
            for (_, _, block) in &stmt.elif_branches {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
            if let Some(block) = &stmt.else_block {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
        }
        Node::For(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::While(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::Loop(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::Skip(stmt) => {
            if let simple_parser::ast::SkipBody::Block(block) = &stmt.body {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
        }
        _ => {}
    }
}

fn validate_basic_type_annotation_block(
    file_path: &Path,
    block: &Block,
    return_type: Option<&Type>,
    errors: &mut Vec<CheckError>,
) {
    for statement in &block.statements {
        validate_basic_type_annotation_node(file_path, statement, return_type, errors);
    }
}

fn declared_type<'a>(explicit: &'a Option<Type>, pattern: &'a Pattern) -> Option<&'a Type> {
    explicit.as_ref().or_else(|| match pattern {
        Pattern::Typed { ty, .. } => Some(ty),
        _ => None,
    })
}

fn validate_literal_type(
    file_path: &Path,
    line: usize,
    column: usize,
    expected: &Type,
    value: &Expr,
    errors: &mut Vec<CheckError>,
) {
    let Some(expected_name) = simple_type_name(expected) else {
        return;
    };
    let Some(found_type) = literal_type_name(value) else {
        return;
    };
    let found_name = found_type.display_name();
    if found_name == "nil" {
        return;
    }
    if type_names_compatible(expected_name, found_name) {
        return;
    }
    if numeric_literal_type_compatible(expected_name, found_type) {
        return;
    }

    errors.push(CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E1003".to_string()),
        message: format!("type mismatch: expected {}, found {}", expected_name, found_name),
        expected: Some(expected_name.to_string()),
        found: Some(found_name.to_string()),
        notes: Vec::new(),
        help: vec!["change the annotation or use a value with the declared type".to_string()],
    });
}

fn simple_type_name(ty: &Type) -> Option<&str> {
    match ty {
        Type::Simple(name) => Some(name.as_str()),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
enum LiteralTypeName {
    Exact(&'static str),
    UnsuffixedInteger,
    UnsuffixedFloat,
}

impl LiteralTypeName {
    fn display_name(self) -> &'static str {
        match self {
            Self::Exact(name) => name,
            Self::UnsuffixedInteger => "i64",
            Self::UnsuffixedFloat => "f64",
        }
    }
}

fn literal_type_name(expr: &Expr) -> Option<LiteralTypeName> {
    match expr {
        Expr::Integer(_) => Some(LiteralTypeName::UnsuffixedInteger),
        Expr::TypedInteger(_, suffix) => Some(LiteralTypeName::Exact(integer_suffix_type_name(suffix))),
        Expr::Float(_) => Some(LiteralTypeName::UnsuffixedFloat),
        Expr::TypedFloat(_, suffix) => Some(LiteralTypeName::Exact(float_suffix_type_name(suffix))),
        Expr::String(_) | Expr::TypedString(_, _) | Expr::FString { .. } => Some(LiteralTypeName::Exact("text")),
        Expr::Bool(_) => Some(LiteralTypeName::Exact("bool")),
        Expr::Nil => Some(LiteralTypeName::Exact("nil")),
        _ => None,
    }
}

fn integer_suffix_type_name(suffix: &NumericSuffix) -> &'static str {
    match suffix {
        NumericSuffix::I8 => "i8",
        NumericSuffix::I16 => "i16",
        NumericSuffix::I32 => "i32",
        NumericSuffix::I64 => "i64",
        NumericSuffix::U8 => "u8",
        NumericSuffix::U16 => "u16",
        NumericSuffix::U32 => "u32",
        NumericSuffix::U64 => "u64",
        NumericSuffix::F32 => "f32",
        NumericSuffix::F64 => "f64",
        NumericSuffix::Unit(_) => "i64",
    }
}

fn float_suffix_type_name(suffix: &NumericSuffix) -> &'static str {
    match suffix {
        NumericSuffix::F32 => "f32",
        NumericSuffix::F64 => "f64",
        NumericSuffix::Unit(_) => "f64",
        NumericSuffix::I8
        | NumericSuffix::I16
        | NumericSuffix::I32
        | NumericSuffix::I64
        | NumericSuffix::U8
        | NumericSuffix::U16
        | NumericSuffix::U32
        | NumericSuffix::U64 => "f64",
    }
}

fn type_names_compatible(expected: &str, found: &str) -> bool {
    is_any_type_name(expected)
        || expected == found
        || matches!(
            (expected, found),
            ("str", "text")
                | ("String", "text")
                | ("Text", "text")
                | ("Bool", "bool")
                | ("Boolean", "bool")
                | ("Int", "i64")
                | ("Integer", "i64")
                | ("Float", "f64")
        )
}

fn numeric_literal_type_compatible(expected: &str, found: LiteralTypeName) -> bool {
    match found {
        LiteralTypeName::UnsuffixedInteger => is_integer_type_name(expected),
        LiteralTypeName::UnsuffixedFloat => is_float_type_name(expected),
        LiteralTypeName::Exact(_) => false,
    }
}

fn is_integer_type_name(name: &str) -> bool {
    matches!(
        name,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "Int"
            | "Integer"
    )
}

fn is_float_type_name(name: &str) -> bool {
    matches!(name, "f32" | "f64" | "Float")
}

fn is_any_type_name(name: &str) -> bool {
    matches!(name, "any" | "Any")
}

fn find_simple_workspace_root(start: &Path) -> Option<PathBuf> {
    let mut current = if start.is_dir() {
        start.to_path_buf()
    } else {
        start.parent()?.to_path_buf()
    };

    loop {
        if current.join("src/compiler").is_dir() && current.join("src/lib").is_dir() {
            return Some(current);
        }
        if !current.pop() {
            return None;
        }
    }
}

/// Validate import statements in a module
fn validate_imports(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>, source_roots: &[PathBuf]) {
    // Create one or more project-aware module resolvers.
    let abs_path = if file_path.is_absolute() {
        file_path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(file_path))
            .unwrap_or_else(|_| file_path.to_path_buf())
    };
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut resolvers = Vec::new();
    if source_roots.is_empty() {
        if let Some(workspace_root) = find_simple_workspace_root(&cwd) {
            let source_root = workspace_root.join("src");
            resolvers.push(ModuleResolver::new(workspace_root, source_root));
        }
        resolvers.push(ModuleResolver::single_file_with_project_hint(&abs_path, Some(&cwd)));
    } else {
        for source_root in source_roots {
            let abs_root = if source_root.is_absolute() {
                source_root.clone()
            } else {
                cwd.join(source_root)
            };
            resolvers.push(ModuleResolver::new(cwd.clone(), abs_root));
        }
    }

    fn target_module_path(
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
    ) -> Option<simple_parser::ast::ModulePath> {
        match target {
            ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
                let mut segments = module_path.segments.clone();
                segments.push(name.clone());
                Some(simple_parser::ast::ModulePath::new(segments))
            }
            _ => None,
        }
    }

    fn target_import_name(target: &ImportTarget) -> Option<&str> {
        match target {
            ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => Some(name),
            _ => None,
        }
    }

    fn target_resolves(
        resolvers: &[ModuleResolver],
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
        from_file: &Path,
    ) -> bool {
        if let ImportTarget::Group(targets) = target {
            return targets
                .iter()
                .all(|target| target_resolves(resolvers, module_path, target, from_file));
        }

        let target_name = target_import_name(target);

        if let Some(candidate_path) = target_module_path(module_path, target) {
            if resolvers
                .iter()
                .any(|resolver| resolver.resolve(&candidate_path, from_file).is_ok())
            {
                return true;
            }
        }

        if let Some(name) = target_name {
            return resolvers.iter().any(|resolver| {
                resolver
                    .resolve(module_path, from_file)
                    .ok()
                    .is_some_and(|resolved| module_file_exports_symbol(&resolved.path, name))
            });
        }

        false
    }

    fn export_target_matches(target: &ImportTarget, name: &str) -> bool {
        match target {
            ImportTarget::Single(exported) | ImportTarget::Aliased { name: exported, .. } => exported == name,
            ImportTarget::Group(targets) => targets.iter().any(|target| export_target_matches(target, name)),
            ImportTarget::Glob => true,
        }
    }

    fn module_file_exports_symbol(path: &Path, name: &str) -> bool {
        let Ok(source) = fs::read_to_string(path) else {
            return false;
        };
        let mut parser = Parser::new(&source);
        let Ok(module) = parser.parse() else {
            return false;
        };

        module.items.iter().any(|item| match item {
            Node::Function(func) => func.name == name,
            Node::Class(class_def) => class_def.name == name,
            Node::Struct(struct_def) => struct_def.name == name,
            Node::Enum(enum_def) => enum_def.name == name,
            Node::Trait(trait_def) => trait_def.name == name,
            Node::ExportUseStmt(export_use) => export_target_matches(&export_use.target, name),
            _ => false,
        })
    }

    fn import_resolves(
        resolvers: &[ModuleResolver],
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
        from_file: &Path,
    ) -> bool {
        if target_resolves(resolvers, module_path, target, from_file) {
            return true;
        }

        if matches!(
            target,
            ImportTarget::Single(_) | ImportTarget::Aliased { .. } | ImportTarget::Group(_)
        ) {
            return false;
        }

        resolvers
            .iter()
            .any(|resolver| resolver.resolve(module_path, from_file).is_ok())
    }

    fn module_resolves(
        resolvers: &[ModuleResolver],
        module_path: &simple_parser::ast::ModulePath,
        from_file: &Path,
    ) -> bool {
        resolvers
            .iter()
            .any(|resolver| resolver.resolve(module_path, from_file).is_ok())
    }

    fn named_target_missing(
        resolvers: &[ModuleResolver],
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
        from_file: &Path,
    ) -> Option<String> {
        match target {
            ImportTarget::Group(targets) => targets
                .iter()
                .find_map(|target| named_target_missing(resolvers, module_path, target, from_file)),
            ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
                if module_resolves(resolvers, module_path, from_file)
                    && !target_resolves(resolvers, module_path, target, from_file)
                {
                    Some(name.clone())
                } else {
                    None
                }
            }
            ImportTarget::Glob => None,
        }
    }

    for item in items {
        match item {
            Node::UseStmt(use_stmt) => {
                if use_stmt.path.segments.is_empty() {
                    continue;
                }
                if let Some(error) = concurrency_api_import_error(
                    file_path,
                    &use_stmt.path,
                    &use_stmt.target,
                    use_stmt.span.line,
                    use_stmt.span.column,
                ) {
                    errors.push(error);
                    continue;
                }
                let resolved = import_resolves(&resolvers, &use_stmt.path, &use_stmt.target, &abs_path);
                if !resolved {
                    if let Some(name) = named_target_missing(&resolvers, &use_stmt.path, &use_stmt.target, &abs_path) {
                        errors.push(CheckError {
                            file: file_path.display().to_string(),
                            line: use_stmt.span.line,
                            column: use_stmt.span.column,
                            severity: ErrorSeverity::Error,
                            code: Some("E0410".to_string()),
                            message: format!(
                                "module '{}' does not export '{}'",
                                use_stmt.path.segments.join("."),
                                name
                            ),
                            expected: Some("exported symbol".to_string()),
                            found: Some(name),
                            notes: Vec::new(),
                            help: vec![
                                "import the symbol from its owning module or update the module export list".to_string(),
                            ],
                        });
                        continue;
                    }
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&use_stmt.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    // Only report as warning since the module might be in a different project location
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: use_stmt.span.line,
                        column: use_stmt.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0410".to_string()),
                        message: format!("unresolved import '{}': {}", use_stmt.path.segments.join("."), msg),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec!["check the module path or add the source root with --source-root".to_string()],
                    });
                }
            }
            Node::MultiUse(multi_use) => {
                for (path, target) in &multi_use.imports {
                    if path.segments.is_empty() {
                        continue;
                    }
                    if let Some(error) = concurrency_api_import_error(
                        file_path,
                        path,
                        target,
                        multi_use.span.line,
                        multi_use.span.column,
                    ) {
                        errors.push(error);
                        continue;
                    }
                    let resolved = import_resolves(&resolvers, path, target, &abs_path);
                    if !resolved {
                        if let Some(name) = named_target_missing(&resolvers, path, target, &abs_path) {
                            errors.push(CheckError {
                                file: file_path.display().to_string(),
                                line: multi_use.span.line,
                                column: multi_use.span.column,
                                severity: ErrorSeverity::Error,
                                code: Some("E0410".to_string()),
                                message: format!("module '{}' does not export '{}'", path.segments.join("."), name),
                                expected: Some("exported symbol".to_string()),
                                found: Some(name),
                                notes: Vec::new(),
                                help: vec![
                                    "import the symbol from its owning module or update the module export list"
                                        .to_string(),
                                ],
                            });
                            continue;
                        }
                        let msg = resolvers
                            .iter()
                            .find_map(|resolver| resolver.resolve(path, &abs_path).err())
                            .map(|e| e.to_string())
                            .unwrap_or_else(|| "unknown import resolution failure".to_string());
                        errors.push(CheckError {
                            file: file_path.display().to_string(),
                            line: multi_use.span.line,
                            column: multi_use.span.column,
                            severity: ErrorSeverity::Warning,
                            code: Some("W0410".to_string()),
                            message: format!("unresolved import '{}': {}", path.segments.join("."), msg),
                            expected: None,
                            found: None,
                            notes: Vec::new(),
                            help: vec!["check the module path or add the source root with --source-root".to_string()],
                        });
                    }
                }
            }
            Node::CommonUseStmt(common_use) => {
                if common_use.path.segments.is_empty() {
                    continue;
                }
                if let Some(error) = concurrency_api_import_error(
                    file_path,
                    &common_use.path,
                    &common_use.target,
                    common_use.span.line,
                    common_use.span.column,
                ) {
                    errors.push(error);
                    continue;
                }
                let resolved = import_resolves(&resolvers, &common_use.path, &common_use.target, &abs_path);
                if !resolved {
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&common_use.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: common_use.span.line,
                        column: common_use.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0411".to_string()),
                        message: format!(
                            "unresolved common import '{}': {}",
                            common_use.path.segments.join("."),
                            msg
                        ),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec!["check the module path or add the source root with --source-root".to_string()],
                    });
                }
            }
            Node::ExportUseStmt(export_use) => {
                if export_use.path.segments.is_empty() {
                    continue;
                }
                if let Some(error) = concurrency_api_import_error(
                    file_path,
                    &export_use.path,
                    &export_use.target,
                    export_use.span.line,
                    export_use.span.column,
                ) {
                    errors.push(error);
                    continue;
                }
                let resolved = import_resolves(&resolvers, &export_use.path, &export_use.target, &abs_path);
                if !resolved {
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&export_use.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: export_use.span.line,
                        column: export_use.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0412".to_string()),
                        message: format!(
                            "unresolved export import '{}': {}",
                            export_use.path.segments.join("."),
                            msg
                        ),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec![
                            "check the exported module path or add the source root with --source-root".to_string(),
                        ],
                    });
                }
            }
            _ => {}
        }
    }
}

fn concurrency_api_import_error(
    file_path: &Path,
    path: &ModulePath,
    target: &ImportTarget,
    line: usize,
    column: usize,
) -> Option<CheckError> {
    let path_text = path.segments.join(".");
    let target_name = match target {
        ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => Some(name),
        ImportTarget::Group(targets) => {
            return targets
                .iter()
                .find_map(|target| concurrency_api_import_error(file_path, path, target, line, column));
        }
        _ => None,
    };

    if is_concurrency_thread_path(&path_text) {
        if let Some(name) = target_name {
            if let Some(replacement) = numbered_concurrency_replacement(name) {
                return Some(numbered_concurrency_error(file_path, line, column, name, replacement));
            }
        }
    }

    let path_symbol = path.segments.split_last().and_then(|(name, owner)| {
        let owner_path = owner.join(".");
        if owner.is_empty() {
            None
        } else {
            Some((owner_path, name))
        }
    });

    if let Some((owner_path, name)) = &path_symbol {
        if is_concurrency_thread_path(owner_path) {
            if let Some(replacement) = numbered_concurrency_replacement(name) {
                return Some(numbered_concurrency_error(file_path, line, column, name, replacement));
            }
        }
    }

    if let Some(name) = target_name {
        if let Some(error) = concurrency_wrong_surface_error(file_path, line, column, &path_text, name) {
            return Some(error);
        }
    } else if let Some((owner_path, name)) = path_symbol {
        if let Some(error) = concurrency_wrong_surface_error(file_path, line, column, &owner_path, name) {
            return Some(error);
        }
    }

    None
}

fn is_concurrency_thread_path(path_text: &str) -> bool {
    matches!(
        path_text,
        "std.concurrent.thread"
            | "std.nogc_async_mut.concurrent.thread"
            | "std.nogc_sync_mut.concurrent.thread"
            | "concurrency.threads"
            | "std.concurrency.threads"
    )
}

fn is_green_thread_path(path_text: &str) -> bool {
    matches!(
        path_text,
        "std.concurrent.green_thread" | "std.nogc_async_mut.concurrent.green_thread"
    )
}

fn numbered_concurrency_replacement(name: &str) -> Option<&'static str> {
    match name {
        "thread_spawn2" => Some("thread_spawn_with_args"),
        "spawn_isolated2" => Some("spawn_isolated_with_args"),
        "spawn_limited2" => Some("spawn_limited_with_args"),
        _ => None,
    }
}

fn numbered_concurrency_error(
    file_path: &Path,
    line: usize,
    column: usize,
    name: &str,
    replacement: &str,
) -> CheckError {
    CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E-PAR-002".to_string()),
        message: format!("{name} is a numbered name and is not a public API"),
        expected: Some("semantic concurrency API symbol".to_string()),
        found: Some(name.to_string()),
        notes: vec![
            "numbered concurrency API names are rejected so OS-thread, cooperative-green, and multicore-green surfaces stay unambiguous"
                .to_string(),
        ],
        help: vec![format!("use {replacement} for explicit-argument spawning")],
    }
}

fn internal_concurrency_runtime_error(file_path: &Path, line: usize, column: usize, name: &str) -> CheckError {
    CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E-PAR-005".to_string()),
        message: format!("{name} is an internal runtime-pool symbol and is not a public API"),
        expected: Some("public multicore-green API symbol".to_string()),
        found: Some(name.to_string()),
        notes: vec![
            "direct rt_pool_* access bypasses the Pure Simple multicore_green facade and cannot provide API-level misuse checks"
                .to_string(),
        ],
        help: vec![
            "use std.concurrent.multicore_green.{multicore_green_spawn, multicore_green_set_parallelism}"
                .to_string(),
        ],
    }
}

fn concurrency_wrong_surface_error(
    file_path: &Path,
    line: usize,
    column: usize,
    owner_path: &str,
    name: &str,
) -> Option<CheckError> {
    if is_concurrency_thread_path(owner_path) && name == "task_spawn" {
        return Some(CheckError {
            file: file_path.display().to_string(),
            line,
            column,
            severity: ErrorSeverity::Error,
            code: Some("E-PAR-001".to_string()),
            message: "task_spawn is not part of the OS-thread facade".to_string(),
            expected: Some("OS-thread API symbol".to_string()),
            found: Some("task_spawn".to_string()),
            notes: vec![
                "std.concurrent.thread is reserved for OS thread primitives such as thread_spawn and thread_spawn_with_args"
                    .to_string(),
            ],
            help: vec!["import task_spawn from std.nogc_async_mut.thread_pool instead".to_string()],
        });
    }

    let Some(expected_owner) = expected_concurrency_owner(name) else {
        return None;
    };

    let accepted = match name {
        "thread_spawn" | "thread_spawn_with_args" => is_concurrency_thread_path(owner_path),
        "green_spawn" => is_green_thread_path(owner_path) || is_cooperative_green_path(owner_path),
        "cooperative_green_spawn"
        | "cooperative_green_spawn_value"
        | "cooperative_green_run_one"
        | "cooperative_green_run_all" => is_cooperative_green_path(owner_path),
        "multicore_green_spawn" => is_multicore_green_path(owner_path),
        "task_spawn" => is_thread_pool_path(owner_path),
        _ => true,
    };

    if accepted {
        return None;
    }

    Some(CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E-PAR-003".to_string()),
        message: format!("{name} belongs to {expected_owner}, not {owner_path}"),
        expected: Some(expected_owner.to_string()),
        found: Some(owner_path.to_string()),
        notes: vec![
            "thread_spawn, green_spawn, cooperative_green_spawn, multicore_green_spawn, and task_spawn intentionally live on separate concurrency surfaces"
                .to_string(),
        ],
        help: vec![format!("import {name} from {expected_owner}")],
    })
}

fn expected_concurrency_owner(name: &str) -> Option<&'static str> {
    match name {
        "thread_spawn" | "thread_spawn_with_args" => Some("std.concurrent.thread"),
        "green_spawn" => Some("std.concurrent.green_thread"),
        "cooperative_green_spawn"
        | "cooperative_green_spawn_value"
        | "cooperative_green_run_one"
        | "cooperative_green_run_all" => Some("std.concurrent.cooperative_green"),
        "multicore_green_spawn" => Some("std.concurrent.multicore_green"),
        "task_spawn" => Some("std.nogc_async_mut.thread_pool"),
        _ => None,
    }
}

fn is_cooperative_green_path(path_text: &str) -> bool {
    matches!(
        path_text,
        "std.concurrent.cooperative_green" | "std.nogc_async_mut.concurrent.cooperative_green"
    )
}

fn is_multicore_green_path(path_text: &str) -> bool {
    matches!(
        path_text,
        "std.concurrent.multicore_green" | "std.nogc_async_mut.concurrent.multicore_green"
    )
}

fn is_thread_pool_path(path_text: &str) -> bool {
    matches!(
        path_text,
        "std.nogc_async_mut.thread_pool" | "nogc_async_mut.thread_pool"
    )
}

/// Convert ParseError to CheckError
fn parse_error_to_check_error(err: &ParseError, path: &Path) -> CheckError {
    use simple_parser::ParseError;
    let diagnostic = err.to_diagnostic();
    let code = diagnostic.code.clone();
    let notes = diagnostic.notes.clone();
    let help = diagnostic.help.clone();

    match err {
        ParseError::SyntaxError {
            message, line, column, ..
        } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: *column,
            severity: ErrorSeverity::Error,
            code,
            message: message.clone(),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::UnexpectedToken {
            expected, found, span, ..
        } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: "unexpected token".to_string(),
            expected: Some(expected.clone()),
            found: Some(found.clone()),
            notes,
            help,
        },
        ParseError::MissingToken { expected, span, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("missing expected token: {}", expected),
            expected: Some(expected.clone()),
            found: None,
            notes,
            help,
        },
        ParseError::UnclosedString { span, .. } => {
            let (line, column) = if let Some(s) = span { (s.line, s.column) } else { (0, 0) };
            CheckError {
                file: path.display().to_string(),
                line,
                column,
                severity: ErrorSeverity::Error,
                code,
                message: "unclosed string literal".to_string(),
                expected: None,
                found: None,
                notes,
                help,
            }
        }
        ParseError::InvalidIndentation { line, .. } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: 1,
            severity: ErrorSeverity::Error,
            code,
            message: "invalid indentation".to_string(),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::InvalidPattern { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("invalid pattern: {}", message),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::InvalidType { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("invalid type: {}", message),
            expected: None,
            found: None,
            notes,
            help,
        },
        _ => CheckError {
            file: path.display().to_string(),
            line: 0,
            column: 0,
            severity: ErrorSeverity::Error,
            code,
            message: err.to_string(),
            expected: None,
            found: None,
            notes,
            help,
        },
    }
}

/// Print error in human-readable format
fn print_error(error: &CheckError) {
    let color = match error.severity {
        ErrorSeverity::Error => "\x1b[31m",   // red
        ErrorSeverity::Warning => "\x1b[33m", // yellow
    };
    let reset = "\x1b[0m";

    let level = match error.severity {
        ErrorSeverity::Error => "error",
        ErrorSeverity::Warning => "warning",
    };
    let code = error
        .code
        .as_ref()
        .map(|code| format!("[{}]", code))
        .unwrap_or_default();
    println!(
        "{}{}:{}:{}: {}{}{}: {}",
        color, error.file, error.line, error.column, level, code, reset, error.message
    );

    if let Some(expected) = &error.expected {
        println!("  expected: {}", expected);
    }
    if let Some(found) = &error.found {
        println!("  found:    {}", found);
    }
    for note in &error.notes {
        println!("  = note: {}", note);
    }
    for help in &error.help {
        println!("  = help: {}", help);
    }
}

/// Output results in JSON format
fn output_json(results: &[FileCheckResult]) {
    let all_errors: Vec<CheckError> = results.iter().flat_map(|r| r.errors.clone()).collect();

    let has_errors = all_errors.iter().any(|error| error.severity == ErrorSeverity::Error);
    let has_warnings = all_errors.iter().any(|error| error.severity == ErrorSeverity::Warning);

    let output = CheckResult {
        status: if has_errors {
            CheckStatus::Error
        } else if has_warnings {
            CheckStatus::Warning
        } else {
            CheckStatus::Success
        },
        files_checked: results.len(),
        errors: all_errors,
    };

    match serde_json::to_string_pretty(&output) {
        Ok(json) => println!("{}", json),
        Err(e) => eprintln!("error: failed to serialize JSON: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_check_valid_code() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x = 42\n    print(x)").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_syntax_error() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x =").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(!result.errors.is_empty());
        assert_eq!(result.errors[0].code.as_deref(), Some("E0002"));
        assert!(!result.errors[0].help.is_empty());
    }

    #[test]
    fn test_check_literal_type_mismatch_is_error() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x: i64 = \"text\"").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert_eq!(result.errors.len(), 1);
        assert_eq!(result.errors[0].severity, ErrorSeverity::Error);
        assert_eq!(result.errors[0].code.as_deref(), Some("E1003"));
        assert_eq!(result.errors[0].expected.as_deref(), Some("i64"));
        assert_eq!(result.errors[0].found.as_deref(), Some("text"));
        assert!(!result.errors[0].help.is_empty());
    }

    #[test]
    fn test_check_reports_short_grammar_warning() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val doubled = nums.map(\\x: x * 2)").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Warning);
        assert_eq!(result.errors.len(), 1);
        assert_eq!(result.errors[0].severity, ErrorSeverity::Warning);
        assert_eq!(result.errors[0].code.as_deref(), Some("L-STYLE-001"));
        assert!(result.errors[0].help.iter().any(|h| h.contains("_1 * 2")));
    }

    #[test]
    fn test_check_matching_literal_type_annotation_succeeds() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x: i64 = 42").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_unsuffixed_integer_annotation_family_succeeds() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x: i32 = 42\n    val y: u32 = 7").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_unsuffixed_float_annotation_family_succeeds() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x: f32 = 1.5").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_return_literal_type_mismatch_is_error() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn value() -> bool:\n    return 1").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert_eq!(result.errors.len(), 1);
        assert_eq!(result.errors[0].code.as_deref(), Some("E1003"));
        assert_eq!(result.errors[0].expected.as_deref(), Some("bool"));
        assert_eq!(result.errors[0].found.as_deref(), Some("i64"));
    }

    #[test]
    fn test_check_common_aliases_and_nil_sentinels_succeed() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "fn main():\n    val flag: Bool = true\n    val value: any = 1\n    val name: text = nil"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_unresolved_import_is_warning() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "use definitely.missing.module\nfn main():\n    val x = 1").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Warning);
        assert_eq!(result.errors.len(), 1);
        assert_eq!(result.errors[0].severity, ErrorSeverity::Warning);
        assert_eq!(result.errors[0].code.as_deref(), Some("W0410"));
        assert!(!result.errors[0].help.is_empty());
    }

    #[test]
    fn test_check_allows_local_manifest_exports() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "export Foo, Bar\nfn Foo() -> i64:\n    return 1").unwrap();

        let result = check_file(file.path(), &[], false);
        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0412")));
    }

    #[test]
    fn test_check_skips_legacy_string_import_paths() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "import \"types\" as Types\nfn main():\n    val x = 1").unwrap();

        let result = check_file(file.path(), &[], false);
        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
    }

    #[test]
    fn test_check_resolves_single_import_target_as_module_path() {
        let dir = tempfile::tempdir().unwrap();
        let lib_root = dir.path().join("src").join("lib");
        let aes = lib_root.join("common").join("aes");
        std::fs::create_dir_all(&aes).unwrap();
        std::fs::write(aes.join("utilities.spl"), "fn helper() -> i64:\n    return 1\n").unwrap();
        let cipher = aes.join("cipher.spl");
        std::fs::write(&cipher, "import aes/utilities\nfn main():\n    val x = 1\n").unwrap();

        let result = check_file(&cipher, &[lib_root], false);
        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
    }

    #[test]
    fn test_check_std_spec_import_resolves_in_project() {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .and_then(Path::parent)
            .expect("driver crate should live under repo/src/compiler_rust")
            .to_path_buf();
        let temp_root = repo_root.join("target/check-tests");
        std::fs::create_dir_all(&temp_root).unwrap();
        let mut file = tempfile::Builder::new().suffix(".spl").tempfile_in(temp_root).unwrap();
        writeln!(file, "use std.spec\nfn main():\n    val x = 1").unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_allows_parallel_os_thread_facade_imports() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.concurrent.thread.{{thread_spawn, thread_spawn_with_args}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_allows_parallel_task_pool_owner_import() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.nogc_async_mut.thread_pool.{{task_spawn}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_rejects_task_spawn_from_os_thread_facade_group_import() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.concurrent.thread.{{task_spawn}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("E-PAR-001")
                && error.message.contains("task_spawn is not part of the OS-thread facade")
        }));
    }

    #[test]
    fn test_check_rejects_task_spawn_from_os_thread_facade_multi_import() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.spec, std.concurrent.thread.{{task_spawn}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result
            .errors
            .iter()
            .any(|error| error.code.as_deref() == Some("E-PAR-001")));
    }

    #[test]
    fn test_check_rejects_task_spawn_from_sync_os_thread_facade() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.nogc_sync_mut.concurrent.thread.{{task_spawn}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result
            .errors
            .iter()
            .any(|error| error.code.as_deref() == Some("E-PAR-001")));
    }

    #[test]
    fn test_check_rejects_numbered_thread_spawn_alias() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.concurrent.thread.{{thread_spawn2}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("E-PAR-002")
                && error.message.contains("thread_spawn2 is a numbered name")
                && error.help.iter().any(|help| help.contains("thread_spawn_with_args"))
        }));
    }

    #[test]
    fn test_check_rejects_numbered_thread_spawn_alias_multi_import() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.spec, std.nogc_sync_mut.concurrent.thread.{{thread_spawn2}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result
            .errors
            .iter()
            .any(|error| error.code.as_deref() == Some("E-PAR-002")));
    }

    #[test]
    fn test_check_rejects_numbered_thread_spawn_alias_common_and_export_use() {
        for statement in [
            "common use std.concurrent.thread.{thread_spawn2}",
            "export use std.concurrent.thread.{thread_spawn2}",
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{statement}\nfn main():\n    val x = 1").unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error);
            assert!(result
                .errors
                .iter()
                .any(|error| error.code.as_deref() == Some("E-PAR-002")));
        }
    }

    #[test]
    fn test_check_rejects_numbered_thread_spawn_alias_with_alias() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.concurrent.thread.{{thread_spawn2 as spawn}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("E-PAR-002")
                && error.help.iter().any(|help| help.contains("thread_spawn_with_args"))
        }));
    }

    #[test]
    fn test_check_rejects_wrong_concurrency_surface_imports() {
        for (statement, symbol, owner) in [
            (
                "use std.concurrent.thread.{cooperative_green_spawn}",
                "cooperative_green_spawn",
                "std.concurrent.cooperative_green",
            ),
            (
                "use std.concurrent.thread.{multicore_green_spawn}",
                "multicore_green_spawn",
                "std.concurrent.multicore_green",
            ),
            (
                "use std.concurrent.thread.{green_spawn}",
                "green_spawn",
                "std.concurrent.green_thread",
            ),
            (
                "use std.concurrent.cooperative_green.{thread_spawn}",
                "thread_spawn",
                "std.concurrent.thread",
            ),
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{statement}\nfn main():\n    val x = 1").unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error);
            assert!(result.errors.iter().any(|error| {
                error.code.as_deref() == Some("E-PAR-003")
                    && error.message.contains(symbol)
                    && error.help.iter().any(|help| help.contains(owner))
            }));
        }
    }

    #[test]
    fn test_check_rejects_bad_concurrency_api_call_shapes() {
        for (source, symbol) in [
            (
                "use std.concurrent.thread.{thread_spawn}\nfn main():\n    val handle = thread_spawn(42)",
                "thread_spawn",
            ),
            (
                "use std.concurrent.green_thread.{green_spawn}\nfn main():\n    val handle = green_spawn(42)",
                "green_spawn",
            ),
            (
                "use std.concurrent.cooperative_green.{cooperative_green_spawn}\nfn main():\n    val handle = cooperative_green_spawn(42)",
                "cooperative_green_spawn",
            ),
            (
                "use std.concurrent.multicore_green.{multicore_green_spawn}\nfn main():\n    val handle = multicore_green_spawn(42)",
                "multicore_green_spawn",
            ),
            (
                "use std.concurrent.multicore_green.{multicore_green_set_parallelism}\nfn main():\n    val workers = multicore_green_set_parallelism(\"4\")",
                "multicore_green_set_parallelism",
            ),
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{source}").unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error, "{source}");
            assert!(result.errors.iter().any(|error| {
                error.code.as_deref() == Some("E-PAR-004") && error.message.contains(symbol)
            }));
        }
    }

    #[test]
    fn test_check_allows_valid_concurrency_api_call_shapes() {
        for source in [
            "use std.concurrent.thread.{thread_spawn}\nfn main():\n    val handle = thread_spawn(\\: 1)",
            "use std.concurrent.green_thread.{green_spawn}\nfn main():\n    val handle = green_spawn(\\: 1)",
            "use std.concurrent.cooperative_green.{green_spawn}\nfn main():\n    val handle = green_spawn(\\: 1)",
            "use std.concurrent.cooperative_green.{cooperative_green_spawn}\nfn main():\n    val handle = cooperative_green_spawn(\\: 1)",
            "use std.concurrent.multicore_green.{multicore_green_spawn}\nfn main():\n    val handle = multicore_green_spawn(\\: 1)",
            "use std.concurrent.multicore_green.{multicore_green_set_parallelism}\nfn main():\n    val workers = multicore_green_set_parallelism(4)",
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{source}").unwrap();

            let result = check_file(file.path(), &[], false);
            assert!(
                result.errors.iter().all(|error| error.code.as_deref() != Some("E-PAR-004")),
                "{source}: {:?}",
                result.errors
            );
        }
    }

    #[test]
    fn test_check_rejects_shared_mutable_state_in_green_closures() {
        for (source, symbol, var_name) in [
            (
                "use std.concurrent.green_thread.{green_spawn}\nvar shared_total = 0\nfn main():\n    val handle = green_spawn(\\: shared_total + 1)",
                "green_spawn",
                "shared_total",
            ),
            (
                "use std.concurrent.cooperative_green.{cooperative_green_spawn}\nvar shared_count = 0\nfn main():\n    val handle = cooperative_green_spawn(\\: shared_count + 1)",
                "cooperative_green_spawn",
                "shared_count",
            ),
            (
                "use std.concurrent.multicore_green.{multicore_green_spawn}\nvar shared_sum = 0\nfn main():\n    val handle = multicore_green_spawn(\\: shared_sum + 1)",
                "multicore_green_spawn",
                "shared_sum",
            ),
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{source}").unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error, "{source}");
            assert!(
                result.errors.iter().any(|error| {
                    error.code.as_deref() == Some("E-PAR-006")
                        && error.message.contains(symbol)
                        && error.message.contains(var_name)
                }),
                "{source}: {:?}",
                result.errors
            );
        }
    }

    #[test]
    fn test_check_allows_share_nothing_green_closures() {
        for source in [
            // Value-only closure stays accepted.
            "use std.concurrent.green_thread.{green_spawn}\nfn main():\n    val handle = green_spawn(\\: 1)",
            // Immutable module-level val is not shared mutable state.
            "use std.concurrent.multicore_green.{multicore_green_spawn}\nval base_value = 10\nfn main():\n    val handle = multicore_green_spawn(\\: base_value + 1)",
            // OS threads may share through locks; thread_spawn stays exempt from E-PAR-006.
            "use std.concurrent.thread.{thread_spawn}\nvar shared_total = 0\nfn main():\n    val handle = thread_spawn(\\: shared_total + 1)",
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "{source}").unwrap();

            let result = check_file(file.path(), &[], false);
            assert!(
                result.errors.iter().all(|error| error.code.as_deref() != Some("E-PAR-006")),
                "{source}: {:?}",
                result.errors
            );
        }
    }

    #[test]
    fn test_check_rejects_numbered_seed_thread_aliases() {
        for (alias, replacement) in [
            ("spawn_isolated2", "spawn_isolated_with_args"),
            ("spawn_limited2", "spawn_limited_with_args"),
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(file, "use concurrency.threads.{{{alias}}}\nfn main():\n    val x = 1").unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error);
            assert!(result.errors.iter().any(|error| {
                error.code.as_deref() == Some("E-PAR-002")
                    && error.message.contains(alias)
                    && error.help.iter().any(|help| help.contains(replacement))
            }));
        }
    }

    #[test]
    fn test_check_rejects_numbered_concurrency_runtime_externs() {
        for (symbol, replacement) in [
            ("rt_thread_spawn_isolated2", "rt_thread_spawn_isolated_with_args"),
            ("rt_thread_spawn_limited2", "rt_thread_spawn_limited_with_args"),
        ] {
            let mut file = NamedTempFile::new().unwrap();
            writeln!(
                file,
                "extern fn {symbol}(closure: Any, data1: Any, data2: Any) -> i64\nfn main():\n    val x = 1"
            )
            .unwrap();

            let result = check_file(file.path(), &[], false);
            assert_eq!(result.status, CheckStatus::Error);
            assert!(result.errors.iter().any(|error| {
                error.code.as_deref() == Some("E-PAR-002")
                    && error.message.contains(symbol)
                    && error.help.iter().any(|help| help.contains(replacement))
            }));
        }
    }

    #[test]
    fn test_check_rejects_missing_group_import_export() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            "use std.concurrent.thread.{{definitely_missing_thread_api}}\nfn main():\n    val x = 1"
        )
        .unwrap();

        let result = check_file(file.path(), &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("E0410")
                && error
                    .message
                    .contains("does not export 'definitely_missing_thread_api'")
        }));
    }

    #[test]
    fn test_check_warns_for_gc_boundary_crossing() {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .and_then(Path::parent)
            .expect("driver crate should live under repo/src/compiler_rust")
            .to_path_buf();
        let temp_dir = repo_root.join("target/gc-boundary-check-tests/src/lib/nogc_sync_mut");
        std::fs::create_dir_all(&temp_dir).unwrap();
        let path = temp_dir.join("gc_boundary_crossing.spl");
        std::fs::write(&path, "use std.gc_async_mut.task\n").unwrap();

        let result = check_file(&path, &[], false);
        assert_eq!(result.status, CheckStatus::Warning);
        assert!(result
            .errors
            .iter()
            .any(|error| error.code.as_deref() == Some("gc_boundary_crossing")));
    }

    #[test]
    fn test_check_can_promote_gc_boundary_crossing_to_error() {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .and_then(Path::parent)
            .expect("driver crate should live under repo/src/compiler_rust")
            .to_path_buf();
        let temp_dir = repo_root.join("target/gc-boundary-check-tests/src/lib/nogc_sync_mut");
        std::fs::create_dir_all(&temp_dir).unwrap();
        let path = temp_dir.join("gc_boundary_crossing_strict.spl");
        std::fs::write(&path, "use std.gc_async_mut.task\n").unwrap();

        let result = check_file(&path, &[], true);
        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("gc_boundary_crossing") && error.severity == ErrorSeverity::Error
        }));
    }

    #[test]
    fn test_baremetal_target_enables_gc_boundary_errors() {
        let options = CheckOptions {
            target: Some(Target::parse("riscv64gc-unknown-none-elf").unwrap()),
            ..CheckOptions::default()
        };

        assert!(should_deny_gc_boundary_crossings(&options));
    }

    #[test]
    fn test_hosted_target_keeps_gc_boundary_warnings_by_default() {
        let options = CheckOptions {
            target: Some(Target::parse("x86_64-unknown-linux-gnu").unwrap()),
            ..CheckOptions::default()
        };

        assert!(!should_deny_gc_boundary_crossings(&options));
    }

    #[test]
    fn test_check_allows_common_runtime_import() {
        let temp_root = tempfile::tempdir().unwrap();
        let lib_root = temp_root.path().join("src/lib");
        let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
        let common_root = lib_root.join("common");
        std::fs::create_dir_all(&noalloc_root).unwrap();
        std::fs::create_dir_all(&common_root).unwrap();
        let path = noalloc_root.join("common_import.spl");
        std::fs::write(&path, "use std.common.text\n").unwrap();
        std::fs::write(common_root.join("text.spl"), "fn value() -> i64:\n    return 1\n").unwrap();

        let result = check_file(&path, &[lib_root], false);
        assert!(result
            .errors
            .iter()
            .all(|error| error.code.as_deref() != Some("gc_boundary_crossing")));
        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
    }

    #[test]
    fn test_strict_noalloc_check_rejects_reachable_allocating_family_import() {
        let temp_root = tempfile::tempdir().unwrap();
        let lib_root = temp_root.path().join("src/lib");
        let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
        std::fs::create_dir_all(&noalloc_root).unwrap();
        let entry = noalloc_root.join("entry.spl");
        let helper = noalloc_root.join("helper.spl");
        std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
        std::fs::write(&helper, "use std.gc_async_mut.task\n").unwrap();

        let result = check_file(&entry, &[lib_root], true);

        assert_eq!(result.status, CheckStatus::Error);
        assert!(result.errors.iter().any(|error| {
            error.code.as_deref() == Some("E0413")
                && error.message.contains("std.gc_async_mut.task")
                && error.file.ends_with("helper.spl")
        }));
    }

    #[test]
    fn test_hosted_noalloc_check_does_not_follow_reachable_import_closure() {
        let temp_root = tempfile::tempdir().unwrap();
        let lib_root = temp_root.path().join("src/lib");
        let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
        std::fs::create_dir_all(&noalloc_root).unwrap();
        let entry = noalloc_root.join("entry.spl");
        let helper = noalloc_root.join("helper.spl");
        std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
        std::fs::write(&helper, "use std.gc_async_mut.task\n").unwrap();

        let result = check_file(&entry, &[lib_root], false);

        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("E0413")));
    }

    #[test]
    fn test_strict_noalloc_check_allows_common_reachable_imports() {
        let temp_root = tempfile::tempdir().unwrap();
        let lib_root = temp_root.path().join("src/lib");
        let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
        let common_root = lib_root.join("common");
        std::fs::create_dir_all(&noalloc_root).unwrap();
        std::fs::create_dir_all(&common_root).unwrap();
        let entry = noalloc_root.join("entry.spl");
        let common = common_root.join("safe_text.spl");
        std::fs::write(&entry, "use std.common.safe_text\n").unwrap();
        std::fs::write(&common, "fn value() -> i64:\n    return 1\n").unwrap();

        let result = check_file(&entry, &[lib_root], true);

        assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("E0413")));
    }

    #[test]
    fn test_check_nonexistent_file() {
        let path = PathBuf::from("/nonexistent/file.spl");
        let result = check_file(&path, &[], false);
        assert_eq!(result.status, CheckStatus::Error);
        assert_eq!(result.errors.len(), 1);
        assert_eq!(result.errors[0].code.as_deref(), Some("E0001"));
        assert!(result.errors[0].message.contains("cannot read file"));
        assert!(!result.errors[0].help.is_empty());
    }
}
