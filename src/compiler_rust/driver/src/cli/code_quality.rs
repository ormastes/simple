//! Code quality commands: lint and format.

use simple_common::diagnostic::{Diagnostic, Diagnostics, EasyFix, FixConfidence, SourceRegistry, Severity, Span};
use simple_common::fix_applicator::FixApplicator;
use simple_compiler::{Formatter, LintChecker, LintConfig};
use simple_parser::ast::{Expr, FunctionDef, Node};
use simple_parser::Parser;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use super::commands::arg_parsing::FixFlags;
use crate::cli::interactive_fix;

const QUALITY_CODES: &[&str] = &[
    "STUB001",
    "STUB003",
    "SSPEC001",
    "SSPEC002",
    "SSPEC003",
    "SSPEC004",
    "SSPEC005",
    "SSPEC006",
];

fn is_test_like_path(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with("_spec.spl") || text.ends_with("_test.spl") || text.contains("/test/") || text.starts_with("test/")
}

fn is_source_like_path(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with(".spl") && !is_test_like_path(path)
}

fn compact(source: &str) -> String {
    source.replace([' ', '\t', '\n', '\r'], "")
}

fn file_allows_lint(source: &str, lint_name: &str) -> bool {
    let normalized = compact(source);
    [
        format!("@allow({})", lint_name),
        format!("@warn({})", lint_name),
        format!("#[allow({})]", lint_name),
        format!("#[warn({})]", lint_name),
        format!("#![allow({})]", lint_name),
        format!("#![warn({})]", lint_name),
    ]
    .into_iter()
    .any(|p| normalized.contains(&p))
}

fn line_span(source: &str, line_index: usize) -> Span {
    let mut start = 0usize;
    for (idx, line) in source.lines().enumerate() {
        if idx == line_index {
            let line_no = idx + 1;
            return Span::new(start, start + line.len(), line_no, 1);
        }
        start += line.len() + 1;
    }
    Span::new(0, 0, 1, 1)
}

fn make_quality_diag(
    file: &Path,
    code: &str,
    line_index: usize,
    message: impl Into<String>,
    help: impl Into<String>,
) -> Diagnostic {
    Diagnostic::error(message.into())
        .with_code(code.to_string())
        .with_file(file.display().to_string())
        .with_label(line_span(&fs::read_to_string(file).unwrap_or_default(), line_index), "")
        .with_help(help.into())
}

fn collect_sspec_quality_diagnostics(path: &Path, source: &str) -> Vec<Diagnostic> {
    if !is_test_like_path(path) {
        return Vec::new();
    }

    let allow_placeholder = file_allows_lint(source, "sspec_placeholder_tests");
    let allow_print_skip = file_allows_lint(source, "sspec_no_print_based_tests");
    let allow_empty = file_allows_lint(source, "sspec_empty_examples");
    let allow_boolean_wrapper = file_allows_lint(source, "sspec_boolean_wrapper_assertions");

    let lines: Vec<&str> = source.lines().collect();
    let mut diagnostics = Vec::new();

    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let normalized = compact(trimmed);

        let tautology = normalized.contains("expect(true).to_equal(true)")
            || normalized.contains("expect(false).to_equal(false)")
            || normalized.contains("expect(true).to_be(true)")
            || normalized.contains("expect(false).to_be(false)");
        if tautology && !allow_placeholder {
            diagnostics.push(
                Diagnostic::error("Tautological assertion in spec/example")
                    .with_code("SSPEC001")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, idx), "")
                    .with_help("Assert returned data, state, or capability outcome instead of a literal boolean"),
            );
        }

        let pass_helper = normalized == "pass_todo"
            || normalized == "pass_do_nothing"
            || normalized == "pass_dn"
            || normalized.contains(":pass_todo")
            || normalized.contains(":pass_do_nothing")
            || normalized.contains(":pass_dn");
        if pass_helper && !allow_placeholder {
            diagnostics.push(
                Diagnostic::error("Placeholder pass helper in spec/example")
                    .with_code("SSPEC002")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, idx), "")
                    .with_help("Use skip: for unsupported environments, or assert a real result"),
            );
        }

        let is_match_arm = trimmed.starts_with("Ok(")
            || trimmed.starts_with("Err(")
            || trimmed.starts_with("case Ok(")
            || trimmed.starts_with("case Err(");
        let has_match_placeholder = tautology
            || normalized.contains(":pass_todo")
            || normalized.contains(":pass_do_nothing")
            || normalized.contains(":pass_dn");
        if is_match_arm && has_match_placeholder && !allow_placeholder {
            diagnostics.push(
                Diagnostic::error("Placeholder success/failure arm in match-based spec assertion")
                    .with_code("SSPEC003")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, idx), "")
                    .with_help("Assert concrete fields from Ok/Err, or use skip: before the match"),
            );
        }

        let print_skip = normalized.contains("print(\"[skip]")
            || normalized.contains("print\"[skip]")
            || normalized.contains("print(\"skip:")
            || normalized.contains("print\"skip:");
        if print_skip && !allow_print_skip {
            diagnostics.push(
                Diagnostic::error("Print-based skip placeholder in spec/example")
                    .with_code("SSPEC004")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, idx), "")
                    .with_help("Use skip: for sanctioned environment skips instead of print-and-return"),
            );
        }

        let boolean_wrapper = (normalized.contains(").to_equal(true)")
            || normalized.contains(").to_equal(false)")
            || normalized.contains(").to_be(true)")
            || normalized.contains(").to_be(false)"))
            && normalized.contains("expect(")
            && (normalized.contains("==")
                || normalized.contains("!=")
                || normalized.contains(">=")
                || normalized.contains("<=")
                || normalized.contains('>')
                || normalized.contains('<'));
        if boolean_wrapper && !allow_boolean_wrapper {
            diagnostics.push(
                Diagnostic::error("Boolean-wrapper assertion in spec/example")
                    .with_code("SSPEC006")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, idx), "")
                    .with_help("Assert the underlying value or capability result instead of expect(<comparison>).to_equal(true/false)"),
            );
        }
    }

    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();
        if !(trimmed.starts_with("it \"") || trimmed.starts_with("slow_it \"")) {
            i += 1;
            continue;
        }

        let header_indent = line.chars().take_while(|ch| *ch == ' ' || *ch == '\t').count();
        let mut j = i + 1;
        let mut statements = Vec::new();
        while j < lines.len() {
            let body_line = lines[j];
            let body_trimmed = body_line.trim();
            let body_indent = body_line.chars().take_while(|ch| *ch == ' ' || *ch == '\t').count();
            if !body_trimmed.is_empty() && !body_trimmed.starts_with('#') && body_indent <= header_indent {
                break;
            }
            if !body_trimmed.is_empty() && !body_trimmed.starts_with('#') {
                statements.push(body_trimmed.to_string());
            }
            j += 1;
        }

        let has_real_assertion = statements.iter().any(|stmt| {
            let normalized = compact(stmt);
            normalized.contains("expect(")
                || normalized.contains("to_equal(")
                || normalized.contains("to_be(")
                || normalized.contains("to_contain(")
                || normalized.contains("to_start_with(")
                || normalized.contains("to_end_with(")
                || normalized.contains("to_be_greater_than(")
                || normalized.contains("to_be_less_than(")
        });
        let has_skip = statements.iter().any(|stmt| {
            let normalized = compact(stmt);
            normalized == "skip:" || normalized.starts_with("skip:") || normalized.contains("return\"skip:") || normalized.contains("return'skip:")
        });

        if statements.is_empty() && !allow_empty {
            diagnostics.push(
                Diagnostic::error("SSpec example has no body")
                    .with_code("SSPEC005")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, i), "")
                    .with_help("Add a real assertion or use skip: for a sanctioned skip"),
            );
        } else if !has_real_assertion && !has_skip && !allow_empty {
            diagnostics.push(
                Diagnostic::error("SSpec example has no real assertion or sanctioned skip")
                    .with_code("SSPEC005")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, i), "")
                    .with_help("Assert a concrete result, or use skip: when the environment legitimately cannot run the example"),
            );
        }

        i = j;
    }

    diagnostics
}

fn single_trivial_expr<'a>(func: &'a FunctionDef) -> Option<&'a Expr> {
    if func.body.statements.len() != 1 {
        return None;
    }
    match &func.body.statements[0] {
        Node::Expression(expr) => Some(expr),
        Node::Return(ret) => ret.value.as_ref(),
        _ => None,
    }
}

fn is_trivial_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Integer(_) | Expr::Float(_) | Expr::String(_) | Expr::Bool(_) | Expr::Nil => true,
        Expr::Array(items) | Expr::Tuple(items) => items.is_empty(),
        Expr::Dict(entries) => entries.is_empty(),
        Expr::Call { callee, args } => matches!(&**callee, Expr::Identifier(name) if name == "Ok") && args.len() == 1 && matches!(args[0].value, Expr::Nil),
        _ => false,
    }
}

fn expr_references_param(expr: &Expr, params: &[String]) -> bool {
    match expr {
        Expr::Identifier(name) => params.iter().any(|param| param == name),
        Expr::Binary { left, right, .. } => expr_references_param(left, params) || expr_references_param(right, params),
        Expr::Unary { operand, .. } => expr_references_param(operand, params),
        Expr::Call { callee, args } => {
            expr_references_param(callee, params) || args.iter().any(|arg| expr_references_param(&arg.value, params))
        }
        Expr::MethodCall { receiver, args, .. } => {
            expr_references_param(receiver, params) || args.iter().any(|arg| expr_references_param(&arg.value, params))
        }
        Expr::FieldAccess { receiver, .. } => expr_references_param(receiver, params),
        Expr::Index { receiver, index } => expr_references_param(receiver, params) || expr_references_param(index, params),
        Expr::TupleIndex { receiver, .. } => expr_references_param(receiver, params),
        Expr::Lambda { body, .. } => expr_references_param(body, params),
        Expr::If { condition, then_branch, else_branch, .. } => {
            expr_references_param(condition, params)
                || expr_references_param(then_branch, params)
                || else_branch.as_ref().is_some_and(|expr| expr_references_param(expr, params))
        }
        Expr::Match { subject, arms } => {
            expr_references_param(subject, params)
                || arms.iter().any(|arm| arm.body.statements.iter().any(|stmt| stmt_references_param(stmt, params)))
        }
        Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => items.iter().any(|item| expr_references_param(item, params)),
        Expr::Dict(entries) => entries.iter().any(|(k, v)| expr_references_param(k, params) || expr_references_param(v, params)),
        Expr::StructInit { fields, spread, .. } => {
            fields.iter().any(|(_, expr)| expr_references_param(expr, params))
                || spread.as_ref().is_some_and(|expr| expr_references_param(expr, params))
        }
        Expr::Cast { expr, .. } | Expr::Spawn(expr) | Expr::Await(expr) | Expr::Spread(expr) | Expr::DictSpread(expr) => {
            expr_references_param(expr, params)
        }
        Expr::DoBlock(statements) => statements.iter().any(|stmt| stmt_references_param(stmt, params)),
        _ => false,
    }
}

fn stmt_references_param(stmt: &Node, params: &[String]) -> bool {
    match stmt {
        Node::Expression(expr) => expr_references_param(expr, params),
        Node::Return(ret) => ret.value.as_ref().is_some_and(|expr| expr_references_param(expr, params)),
        Node::Let(let_stmt) => let_stmt.value.as_ref().is_some_and(|expr| expr_references_param(expr, params)),
        Node::Assignment(assign) => expr_references_param(&assign.target, params) || expr_references_param(&assign.value, params),
        Node::If(if_stmt) => {
            expr_references_param(&if_stmt.condition, params)
                || if_stmt.then_block.statements.iter().any(|stmt| stmt_references_param(stmt, params))
                || if_stmt.elif_branches.iter().any(|(_, expr, block)| {
                    expr_references_param(expr, params) || block.statements.iter().any(|stmt| stmt_references_param(stmt, params))
                })
                || if_stmt.else_block.as_ref().is_some_and(|block| block.statements.iter().any(|stmt| stmt_references_param(stmt, params)))
        }
        Node::Match(match_stmt) => {
            expr_references_param(&match_stmt.subject, params)
                || match_stmt.arms.iter().any(|arm| arm.body.statements.iter().any(|stmt| stmt_references_param(stmt, params)))
        }
        Node::For(for_stmt) => expr_references_param(&for_stmt.iterable, params) || for_stmt.body.statements.iter().any(|stmt| stmt_references_param(stmt, params)),
        Node::While(while_stmt) => expr_references_param(&while_stmt.condition, params) || while_stmt.body.statements.iter().any(|stmt| stmt_references_param(stmt, params)),
        Node::Loop(loop_stmt) => loop_stmt.body.statements.iter().any(|stmt| stmt_references_param(stmt, params)),
        _ => false,
    }
}

fn collect_stub_diagnostics_for_function(path: &Path, func: &FunctionDef) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    if func.name.starts_with("_noop_") || func.body.statements.is_empty() {
        return diagnostics;
    }
    if file_allows_lint(&fs::read_to_string(path).unwrap_or_default(), "stub_impl") {
        return diagnostics;
    }

    let first_stmt = &func.body.statements[0];
    if func.body.statements.len() == 1 && matches!(first_stmt, Node::Pass(_)) {
        diagnostics.push(
            Diagnostic::error("Explicit placeholder function body")
                .with_code("STUB003")
                .with_file(path.display().to_string())
                .with_label(func.span.into(), "")
                .with_help("Replace the placeholder body with a real implementation or add an explicit allow override"),
        );
        return diagnostics;
    }

    if func.params.is_empty() {
        return diagnostics;
    }

    if let Some(expr) = single_trivial_expr(func) {
        if is_trivial_expr(expr) {
            let param_names: Vec<String> = func.params.iter().map(|p| p.name.clone()).collect();
            let references_param = func.body.statements.iter().any(|stmt| stmt_references_param(stmt, &param_names));
            if !references_param {
                diagnostics.push(
                    Diagnostic::error("Trivial return with unused parameters — possible stub")
                        .with_code("STUB001")
                        .with_file(path.display().to_string())
                        .with_label(func.span.into(), "")
                        .with_help("Replace the trivial body with a real implementation or mark the file/function with an explicit allow override"),
                );
            }
        }
    }

    diagnostics
}

fn collect_stub_diagnostics(path: &Path, items: &[Node]) -> Vec<Diagnostic> {
    if !is_source_like_path(path) {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    for item in items {
        match item {
            Node::Function(func) => diagnostics.extend(collect_stub_diagnostics_for_function(path, func)),
            Node::Struct(s) => {
                for method in &s.methods {
                    diagnostics.extend(collect_stub_diagnostics_for_function(path, method));
                }
            }
            Node::Class(c) => {
                for method in &c.methods {
                    diagnostics.extend(collect_stub_diagnostics_for_function(path, method));
                }
            }
            Node::Impl(imp) => {
                for method in &imp.methods {
                    diagnostics.extend(collect_stub_diagnostics_for_function(path, method));
                }
            }
            _ => {}
        }
    }
    diagnostics
}

fn collect_extra_quality_diagnostics(path: &Path, source: &str, items: &[Node]) -> Vec<Diagnostic> {
    let mut diagnostics = collect_sspec_quality_diagnostics(path, source);
    diagnostics.extend(collect_stub_diagnostics(path, items));
    diagnostics
}

fn is_quality_diagnostic(diag: &Diagnostic) -> bool {
    diag.code
        .as_deref()
        .is_some_and(|code| QUALITY_CODES.contains(&code))
}

pub fn run_verify_quality(args: &[String]) -> i32 {
    let mut full_project = false;
    let mut paths: Vec<PathBuf> = Vec::new();

    for arg in args {
        if arg == "--all" {
            full_project = true;
        } else if !arg.starts_with('-') {
            paths.push(PathBuf::from(arg));
        }
    }

    let mut files = Vec::new();
    if full_project {
        for root in ["src", "test"] {
            let path = PathBuf::from(root);
            if path.exists() {
                for entry in WalkDir::new(&path)
                    .follow_links(true)
                    .into_iter()
                    .filter_map(|e| e.ok())
                    .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
                {
                    files.push(entry.path().to_path_buf());
                }
            }
        }
    } else {
        files = paths;
    }

    if files.is_empty() {
        eprintln!("error: verify quality requires file paths or --all");
        eprintln!("Usage: simple verify quality [--all] [file ...]");
        return 1;
    }

    let mut total = 0usize;
    let mut failures = 0usize;
    for file in files {
        total += 1;
        match lint_file_internal(&file, true) {
            Some((_has_errors, _err_count, _warn_count, diagnostics, _fixes, _source)) => {
                let quality: Vec<_> = diagnostics.into_iter().filter(is_quality_diagnostic).collect();
                if quality.is_empty() {
                    println!("quality: {} OK", file.display());
                } else {
                    failures += 1;
                    for diag in quality {
                        let code = diag.code.unwrap_or_else(|| "QUALITY".to_string());
                        let line = diag.labels.first().map(|label| label.span.line).unwrap_or(1);
                        println!("{}:{}: error[{}]: {}", file.display(), line, code, diag.message);
                        for help in diag.help {
                            println!("  help: {}", help);
                        }
                    }
                }
            }
            None => {
                failures += 1;
                eprintln!("error: failed to lint {}", file.display());
            }
        }
    }

    println!();
    if failures == 0 {
        println!("Verify quality passed: {} file(s) clean", total);
        0
    } else {
        println!("Verify quality failed: {} file(s) with anti-dummy / anti-stub findings", failures);
        1
    }
}

/// Run the linter on a file or directory
pub fn run_lint(args: &[String]) -> i32 {
    // Parse arguments
    let path = args.get(1).map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
    let json_output = args.iter().any(|a| a == "--json");
    let fix_flags = FixFlags::parse(args);

    // Check if path is directory
    if path.is_dir() {
        return lint_directory(&path, json_output, &fix_flags);
    }

    // Lint single file
    lint_file(&path, json_output, &fix_flags)
}

/// Lint all .spl files in a directory
pub fn lint_directory(dir: &PathBuf, json_output: bool, fix_flags: &FixFlags) -> i32 {
    let mut all_errors = false;
    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut all_diags = Diagnostics::new();
    let mut all_fixes: Vec<EasyFix> = Vec::new();
    let mut sources = SourceRegistry::new();

    for entry in WalkDir::new(dir)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
    {
        let path = entry.path();
        let result = lint_file_internal(path, false);

        if let Some((has_err, err_count, warn_count, diags, fixes, source)) = result {
            if has_err {
                all_errors = true;
            }
            total_errors += err_count;
            total_warnings += warn_count;

            if json_output {
                for diag in diags {
                    all_diags.push(diag);
                }
            }

            all_fixes.extend(fixes);
            if let Some(src) = source {
                sources.add(path.display().to_string(), src);
            }
        }
    }

    // Apply fixes if requested
    if fix_flags.any_fix_mode() && !all_fixes.is_empty() {
        apply_fixes(&all_fixes, &sources, fix_flags);
    }

    if json_output {
        match all_diags.to_json() {
            Ok(json) => println!("{}", json),
            Err(e) => {
                eprintln!("error: failed to serialize diagnostics: {}", e);
                return 1;
            }
        }
    } else {
        println!();
        println!(
            "Total: {} error(s), {} warning(s) across {} file(s)",
            total_errors,
            total_warnings,
            WalkDir::new(dir)
                .into_iter()
                .filter(|e| e
                    .as_ref()
                    .ok()
                    .and_then(|e| e.path().extension().and_then(|s| s.to_str()))
                    == Some("spl"))
                .count()
        );
    }

    if all_errors {
        1
    } else {
        0
    }
}

/// Lint a single file
pub fn lint_file(path: &Path, json_output: bool, fix_flags: &FixFlags) -> i32 {
    if let Some((has_errors, _, _, diags, fixes, source)) = lint_file_internal(path, json_output) {
        // Apply fixes if requested
        if fix_flags.any_fix_mode() && !fixes.is_empty() {
            let mut sources = SourceRegistry::new();
            if let Some(src) = source {
                sources.add(path.display().to_string(), src);
            }
            apply_fixes(&fixes, &sources, fix_flags);
        }

        if json_output {
            let mut all_diags = Diagnostics::new();
            for diag in diags {
                all_diags.push(diag);
            }
            match all_diags.to_json() {
                Ok(json) => println!("{}", json),
                Err(e) => {
                    eprintln!("error: failed to serialize diagnostics: {}", e);
                    return 1;
                }
            }
        }
        if has_errors {
            1
        } else {
            0
        }
    } else {
        1
    }
}

/// Result of internal lint operation
pub type LintResult = (
    bool,
    usize,
    usize,
    Vec<simple_common::diagnostic::Diagnostic>,
    Vec<EasyFix>,
    Option<String>,
);

/// Internal lint function that returns diagnostic information
/// Returns: (has_errors, error_count, warning_count, diagnostics, easy_fixes, source_text)
pub fn lint_file_internal(path: &std::path::Path, json_output: bool) -> Option<LintResult> {
    // Read file
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            if !json_output {
                eprintln!("error: cannot read {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Parse file
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            if !json_output {
                eprintln!("error: parse failed in {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Create lint checker
    let config = LintConfig::default();
    let mut checker = LintChecker::with_config(config).with_source_file(Some(path.to_path_buf()));

    // Run lint checks
    checker.check_module(&module.items);
    let diagnostics = checker.diagnostics();

    let error_count = diagnostics.iter().filter(|d| d.is_error()).count();
    let warning_count = diagnostics.len() - error_count;
    let has_errors = error_count > 0;

    // Convert to common diagnostics
    let mut common_diags: Vec<simple_common::diagnostic::Diagnostic> = diagnostics
        .iter()
        .map(|d| d.to_diagnostic(Some(path.display().to_string())))
        .collect();
    common_diags.extend(collect_extra_quality_diagnostics(path, &source, &module.items));

    // Collect easy fixes from diagnostics
    let easy_fixes: Vec<EasyFix> = diagnostics.iter().filter_map(|d| d.easy_fix.clone()).collect();

    if json_output {
        // Return diagnostics for aggregation
    } else {
        // Human-readable output
        if common_diags.is_empty() {
            println!("{}: OK", path.display());
        } else {
            for diagnostic in &common_diags {
                // Format: file:line:col: level: message
                let (line, column) = diagnostic
                    .labels
                    .first()
                    .map(|label| (label.span.line, label.span.column))
                    .unwrap_or((1, 1));
                let level_str = if matches!(diagnostic.severity, Severity::Error) { "error" } else { "warning" };
                let code = diagnostic.code.clone().unwrap_or_else(|| "lint".to_string());
                println!(
                    "{}:{}:{}: {}: {} [{}]",
                    path.display(),
                    line,
                    column,
                    level_str,
                    diagnostic.message,
                    code
                );
                for help in &diagnostic.help {
                    println!("  help: {}", help);
                }
                if diagnostic.easy_fix.is_some() {
                    println!("  fix: available (use --fix to apply)");
                }
            }
        }
    }

    Some((
        common_diags.iter().any(|d| matches!(d.severity, Severity::Error)),
        common_diags.iter().filter(|d| matches!(d.severity, Severity::Error)).count(),
        common_diags.iter().filter(|d| !matches!(d.severity, Severity::Error)).count(),
        common_diags,
        easy_fixes,
        Some(source),
    ))
}

/// Apply collected fixes based on fix flags
fn apply_fixes(fixes: &[EasyFix], sources: &SourceRegistry, fix_flags: &FixFlags) {
    // Filter fixes based on flags
    let filtered: Vec<&EasyFix> = if fix_flags.fix_all {
        fixes.iter().collect()
    } else if fix_flags.fix {
        FixApplicator::filter_by_confidence(fixes, FixConfidence::Safe)
    } else if let Some(ref id) = fix_flags.fix_id {
        FixApplicator::filter_by_id(fixes, id)
    } else if let Some(ref code) = fix_flags.fix_code {
        fixes.iter().filter(|f| f.id.starts_with(code)).collect()
    } else if let Some(nth) = fix_flags.fix_nth {
        if nth > 0 && nth <= fixes.len() {
            vec![&fixes[nth - 1]]
        } else {
            eprintln!("error: --fix-nth={} is out of range (1-{})", nth, fixes.len());
            return;
        }
    } else {
        // Default: safe fixes only
        FixApplicator::filter_by_confidence(fixes, FixConfidence::Safe)
    };

    if filtered.is_empty() {
        println!("No applicable fixes found.");
        return;
    }

    // Interactive mode
    if fix_flags.fix_interactive {
        let accepted = interactive_fix::prompt_fixes(&filtered);
        if accepted.is_empty() {
            println!("No fixes applied.");
            return;
        }
        let owned: Vec<EasyFix> = accepted.into_iter().cloned().collect();
        match FixApplicator::apply_to_disk(&owned, sources, fix_flags.fix_dry_run) {
            Ok(report) => print_fix_report(&report, fix_flags.fix_dry_run),
            Err(e) => eprintln!("error applying fixes: {}", e),
        }
        return;
    }

    // Non-interactive: apply all filtered fixes
    let owned: Vec<EasyFix> = filtered.into_iter().cloned().collect();
    match FixApplicator::apply_to_disk(&owned, sources, fix_flags.fix_dry_run) {
        Ok(report) => print_fix_report(&report, fix_flags.fix_dry_run),
        Err(e) => eprintln!("error applying fixes: {}", e),
    }
}

fn print_fix_report(report: &simple_common::fix_applicator::FixReport, dry_run: bool) {
    let prefix = if dry_run { "Would apply" } else { "Applied" };
    println!("{} {} fix(es):", prefix, report.applied);
    for detail in &report.details {
        println!("  {}", detail);
    }
    if !report.modified_files.is_empty() {
        let verb = if dry_run { "Would modify" } else { "Modified" };
        println!("{} {} file(s):", verb, report.modified_files.len());
        for file in &report.modified_files {
            println!("  {}", file);
        }
    }
}

/// Run the formatter on a file or directory
pub fn run_fmt(args: &[String]) -> i32 {
    // Parse arguments
    let path = args.get(1).map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Format the source code
    let mut formatter = Formatter::new();
    let formatted = match formatter.format_source(&source) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    if check_only {
        // Check if file is already formatted
        if source == formatted {
            println!("{}: formatted correctly", path.display());
            0
        } else {
            eprintln!("{}: needs formatting", path.display());
            1
        }
    } else {
        // Write formatted code back to file
        match fs::write(&path, &formatted) {
            Ok(_) => {
                println!("{}: formatted", path.display());
                0
            }
            Err(e) => {
                eprintln!("error: cannot write {}: {}", path.display(), e);
                1
            }
        }
    }
}
