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
    "STUB001", "STUB003", "SPIPE001", "SPIPE002", "SPIPE003", "SPIPE004", "SPIPE005", "SPIPE006", "UI001", "UI002",
    "UI003",
];

fn is_test_like_path(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with("_spec.spl") || text.ends_with("_test.spl") || text.contains("/test/") || text.starts_with("test/")
}

fn is_source_like_path(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with(".spl") && !is_test_like_path(path)
}

fn is_theme_package_lint_path(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.contains("config/themes/")
        && matches!(
            path.extension().and_then(|s| s.to_str()),
            Some("sdn") | Some("css") | Some("html")
        )
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

fn collect_spipe_quality_diagnostics(path: &Path, source: &str) -> Vec<Diagnostic> {
    if !is_test_like_path(path) {
        return Vec::new();
    }

    let allow_placeholder = file_allows_lint(source, "spipe_placeholder_tests");
    let allow_print_skip = file_allows_lint(source, "spipe_no_print_based_tests");
    let allow_empty = file_allows_lint(source, "spipe_empty_examples");
    let allow_boolean_wrapper = file_allows_lint(source, "spipe_boolean_wrapper_assertions");

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
                    .with_code("SPIPE001")
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
                    .with_code("SPIPE002")
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
                    .with_code("SPIPE003")
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
                    .with_code("SPIPE004")
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
                    .with_code("SPIPE006")
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
            normalized == "skip:"
                || normalized.starts_with("skip:")
                || normalized.contains("return\"skip:")
                || normalized.contains("return'skip:")
        });

        if statements.is_empty() && !allow_empty {
            diagnostics.push(
                Diagnostic::error("SPipe example has no body")
                    .with_code("SPIPE005")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, i), "")
                    .with_help("Add a real assertion or use skip: for a sanctioned skip"),
            );
        } else if !has_real_assertion && !has_skip && !allow_empty {
            diagnostics.push(
                Diagnostic::error("SPipe example has no real assertion or sanctioned skip")
                    .with_code("SPIPE005")
                    .with_file(path.display().to_string())
                    .with_label(line_span(source, i), "")
                    .with_help("Assert a concrete result, or use skip: when the environment legitimately cannot run the example"),
            );
        }

        i = j;
    }

    diagnostics
}

fn single_trivial_expr(func: &FunctionDef) -> Option<&Expr> {
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
        Expr::Call { callee, args } => {
            matches!(&**callee, Expr::Identifier(name) if name == "Ok")
                && args.len() == 1
                && matches!(args[0].value, Expr::Nil)
        }
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
        Expr::Index { receiver, index } => {
            expr_references_param(receiver, params) || expr_references_param(index, params)
        }
        Expr::TupleIndex { receiver, .. } => expr_references_param(receiver, params),
        Expr::Lambda { body, .. } => expr_references_param(body, params),
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            expr_references_param(condition, params)
                || expr_references_param(then_branch, params)
                || else_branch
                    .as_ref()
                    .is_some_and(|expr| expr_references_param(expr, params))
        }
        Expr::Match { subject, arms } => {
            expr_references_param(subject, params)
                || arms.iter().any(|arm| {
                    arm.body
                        .statements
                        .iter()
                        .any(|stmt| stmt_references_param(stmt, params))
                })
        }
        Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => {
            items.iter().any(|item| expr_references_param(item, params))
        }
        Expr::Dict(entries) => entries
            .iter()
            .any(|(k, v)| expr_references_param(k, params) || expr_references_param(v, params)),
        Expr::StructInit { fields, spread, .. } => {
            fields.iter().any(|(_, expr)| expr_references_param(expr, params))
                || spread.as_ref().is_some_and(|expr| expr_references_param(expr, params))
        }
        Expr::Cast { expr, .. }
        | Expr::Spawn(expr)
        | Expr::Await(expr)
        | Expr::Spread(expr)
        | Expr::DictSpread(expr) => expr_references_param(expr, params),
        Expr::DoBlock(statements) => statements.iter().any(|stmt| stmt_references_param(stmt, params)),
        _ => false,
    }
}

fn stmt_references_param(stmt: &Node, params: &[String]) -> bool {
    match stmt {
        Node::Expression(expr) => expr_references_param(expr, params),
        Node::Return(ret) => ret
            .value
            .as_ref()
            .is_some_and(|expr| expr_references_param(expr, params)),
        Node::Let(let_stmt) => let_stmt
            .value
            .as_ref()
            .is_some_and(|expr| expr_references_param(expr, params)),
        Node::Assignment(assign) => {
            expr_references_param(&assign.target, params) || expr_references_param(&assign.value, params)
        }
        Node::If(if_stmt) => {
            expr_references_param(&if_stmt.condition, params)
                || if_stmt
                    .then_block
                    .statements
                    .iter()
                    .any(|stmt| stmt_references_param(stmt, params))
                || if_stmt.elif_branches.iter().any(|(_, expr, block)| {
                    expr_references_param(expr, params)
                        || block.statements.iter().any(|stmt| stmt_references_param(stmt, params))
                })
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.statements.iter().any(|stmt| stmt_references_param(stmt, params)))
        }
        Node::Match(match_stmt) => {
            expr_references_param(&match_stmt.subject, params)
                || match_stmt.arms.iter().any(|arm| {
                    arm.body
                        .statements
                        .iter()
                        .any(|stmt| stmt_references_param(stmt, params))
                })
        }
        Node::For(for_stmt) => {
            expr_references_param(&for_stmt.iterable, params)
                || for_stmt
                    .body
                    .statements
                    .iter()
                    .any(|stmt| stmt_references_param(stmt, params))
        }
        Node::While(while_stmt) => {
            expr_references_param(&while_stmt.condition, params)
                || while_stmt
                    .body
                    .statements
                    .iter()
                    .any(|stmt| stmt_references_param(stmt, params))
        }
        Node::Loop(loop_stmt) => loop_stmt
            .body
            .statements
            .iter()
            .any(|stmt| stmt_references_param(stmt, params)),
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
            let references_param = func
                .body
                .statements
                .iter()
                .any(|stmt| stmt_references_param(stmt, &param_names));
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

fn make_quality_warn_diag(
    file: &Path,
    code: &str,
    line_index: usize,
    message: impl Into<String>,
    help: impl Into<String>,
) -> Diagnostic {
    Diagnostic::warning(message.into())
        .with_code(code.to_string())
        .with_file(file.display().to_string())
        .with_label(line_span(&fs::read_to_string(file).unwrap_or_default(), line_index), "")
        .with_help(help.into())
}

/// Allowlisted paths for UI001 (raw widget kind).
fn is_ui001_allowlisted(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.contains("common/ui/parse/")
        || text.contains("os/services/llm/widget_eval")
        || text.ends_with("common/ui/builder.spl")
        || text.ends_with("common/ui/ios/builder.spl")
        || text.ends_with("common/ui/glass/builder.spl")
}

/// Allowlisted paths for UI002 (raw variant).
fn is_ui002_allowlisted(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with("common/ui/builder.spl") || text.ends_with("common/ui/glass/builder.spl")
}

/// Allowlisted paths for UI003 (raw theme name).
fn is_ui003_allowlisted(path: &Path) -> bool {
    let text = path.to_string_lossy();
    text.ends_with("common/ui/style.spl") || is_test_like_path(path)
}

/// UI001 — flag raw string literal as WidgetNode kind arg.
/// UI002 — flag raw string literal in with_on_typed_action action position or toast variant.
/// UI003 — flag raw theme-name string literals.
fn collect_ui_typed_api_diagnostics(path: &Path, source: &str) -> Vec<Diagnostic> {
    let ui001_ok = is_ui001_allowlisted(path);
    let ui002_ok = is_ui002_allowlisted(path);
    let ui003_ok = is_ui003_allowlisted(path);

    if ui001_ok && ui002_ok && ui003_ok {
        return Vec::new();
    }

    let theme_names = [
        "ios_light",
        "ios_dark",
        "glass_light",
        "glass_dark",
        "glass_obsidian_dark",
        "simple_dark",
        "simple_light",
    ];

    let mut diagnostics = Vec::new();

    for (idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        // UI001: WidgetNode.new(<id>, "<literal>")
        if !ui001_ok {
            if let Some(call_pos) = trimmed.find("WidgetNode.new(") {
                let after_paren = &trimmed[call_pos + 15..];
                if let Some(comma) = after_paren.find(',') {
                    let kind_part = after_paren[comma + 1..].trim_start();
                    if kind_part.starts_with('"') {
                        diagnostics.push(make_quality_warn_diag(
                            path,
                            "UI001",
                            idx,
                            "Raw string literal as WidgetNode kind — use WidgetKind.X.to_wire()",
                            "Replace the string literal with WidgetKind.<Variant>.to_wire(), e.g. WidgetKind.Panel.to_wire()",
                        ));
                    }
                }
            }
        }

        // UI002: with_on_typed_action(<node>, "<literal>") or toast(<id>, <msg>, "<literal>")
        if !ui002_ok {
            if let Some(call_pos) = trimmed.find("with_on_typed_action(") {
                let after_paren = &trimmed[call_pos + 21..];
                if let Some(comma) = after_paren.find(',') {
                    let action_part = after_paren[comma + 1..].trim_start();
                    if action_part.starts_with('"') {
                        diagnostics.push(make_quality_warn_diag(
                            path,
                            "UI002",
                            idx,
                            "Raw string literal in action position — use Action or CommonAction",
                            "Replace the string literal with CommonAction.Save.into_action() or Action.Custom(name: \"...\")",
                        ));
                    }
                }
            }
            if let Some(call_pos) = trimmed.find("toast(") {
                // Only flag "toast(" not "show_toast(" etc.
                let before = &trimmed[..call_pos];
                let is_method_call = before.ends_with('.') || before.ends_with("self.");
                let is_standalone =
                    call_pos == 0 || !before.chars().last().map_or(false, |c| c.is_alphanumeric() || c == '_');
                if is_method_call || is_standalone {
                    let after_paren = &trimmed[call_pos + 6..];
                    // Find third arg (skip two commas)
                    if let Some(c1) = after_paren.find(',') {
                        let after_first = &after_paren[c1 + 1..];
                        if let Some(c2) = after_first.find(',') {
                            let variant_part = after_first[c2 + 1..].trim_start();
                            if variant_part.starts_with('"') {
                                diagnostics.push(make_quality_warn_diag(
                                    path,
                                    "UI002",
                                    idx,
                                    "Raw string literal as toast variant — use a typed constant when StatusVariant is available",
                                    "Replace the string literal variant with a typed constant once StatusVariant lands",
                                ));
                            }
                        }
                    }
                }
            }
        }

        // UI003: raw theme-name string literals
        if !ui003_ok {
            for theme_name in &theme_names {
                let quoted = format!("\"{}\"", theme_name);
                if trimmed.contains(&quoted) {
                    diagnostics.push(make_quality_warn_diag(
                        path,
                        "UI003",
                        idx,
                        format!("Raw theme-name string \"{}\" — use ThemeId enum variant", theme_name),
                        format!(
                            "Replace \"{}\" with the ThemeId variant, e.g. ThemeId.IOSLight",
                            theme_name
                        ),
                    ));
                    break; // one diagnostic per line
                }
            }
        }
    }

    diagnostics
}

fn collect_extra_quality_diagnostics(path: &Path, source: &str, items: &[Node]) -> Vec<Diagnostic> {
    let mut diagnostics = collect_spipe_quality_diagnostics(path, source);
    diagnostics.extend(collect_stub_diagnostics(path, items));
    diagnostics.extend(collect_ui_typed_api_diagnostics(path, source));
    diagnostics
}

fn is_quality_diagnostic(diag: &Diagnostic) -> bool {
    diag.code.as_deref().is_some_and(|code| QUALITY_CODES.contains(&code))
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
        println!(
            "Verify quality failed: {} file(s) with anti-dummy / anti-stub findings",
            failures
        );
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

/// Lint all .spl files and theme package files in a directory
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
        .filter(|e| {
            e.path().extension().and_then(|s| s.to_str()) == Some("spl") || is_theme_package_lint_path(e.path())
        })
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
                    .map(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl")
                        || is_theme_package_lint_path(e.path()))
                    == Some(true))
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

fn theme_root_value(content: &str, key: &str) -> String {
    let prefix = format!("{}:", key);
    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix(&prefix) {
            return rest.trim().trim_matches('"').to_string();
        }
    }
    String::new()
}

fn theme_section_value(content: &str, section: &str, key: &str) -> String {
    let mut current = "";
    let section_header = format!("{}:", section);
    let prefix = format!("{}:", key);
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if trimmed == section_header {
            current = section;
            continue;
        }
        if !line.starts_with(' ') && trimmed.ends_with(':') {
            current = trimmed.trim_end_matches(':');
            continue;
        }
        if current == section {
            if let Some(rest) = trimmed.strip_prefix(&prefix) {
                return rest.trim().trim_matches('"').to_string();
            }
        }
    }
    String::new()
}

fn theme_section_items(content: &str, section: &str) -> Vec<String> {
    let mut current = "";
    let section_header = format!("{}:", section);
    let mut items = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if trimmed == section_header {
            current = section;
            continue;
        }
        if !line.starts_with(' ') && trimmed.ends_with(':') {
            current = trimmed.trim_end_matches(':');
            continue;
        }
        if current == section {
            if let Some(rest) = trimmed.strip_prefix("- ") {
                items.push(rest.trim().trim_matches('"').to_string());
            }
        }
    }
    items
}

fn theme_defined_tokens(css: &str) -> Vec<String> {
    css.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("--") && line.contains(':'))
        .filter_map(|line| line.split(':').next().map(|s| s.trim().to_string()))
        .collect()
}

fn theme_validate_refs(path: &str, content: &str, tokens: &[String], issues: &mut Vec<(String, String, String)>) {
    let mut rest = content;
    while let Some(idx) = rest.find("var(--") {
        let tail = &rest[idx + 4..];
        let Some(end) = tail.find(')') else {
            break;
        };
        let token = tail[..end].trim();
        if !tokens.iter().any(|t| t == token) {
            issues.push((
                path.to_string(),
                token.to_string(),
                "unresolved CSS token reference".to_string(),
            ));
        }
        rest = &tail[end + 1..];
    }
}

fn validate_theme_package_for_lint() -> Vec<(String, String, String)> {
    let registry_path = PathBuf::from("config/themes/theme.sdn");
    let mut issues = Vec::new();
    let Ok(registry) = fs::read_to_string(&registry_path) else {
        issues.push((
            "config/themes/theme.sdn".to_string(),
            "registry".to_string(),
            "theme registry file is missing".to_string(),
        ));
        return issues;
    };

    let default_id = theme_root_value(&registry, "default_theme");
    if default_id.is_empty() {
        issues.push((
            "config/themes/theme.sdn".to_string(),
            "default_theme".to_string(),
            "default_theme is required".to_string(),
        ));
    }
    let theme_id = if default_id.is_empty() {
        "aetheric_dark".to_string()
    } else {
        default_id
    };
    let theme_path = theme_section_value(&registry, "themes", &theme_id);
    if theme_path.is_empty() {
        issues.push((
            "config/themes/theme.sdn".to_string(),
            format!("themes.{}", theme_id),
            "default theme is not listed in themes".to_string(),
        ));
        return issues;
    }
    let Ok(theme_sdn) = fs::read_to_string(&theme_path) else {
        issues.push((
            theme_path,
            format!("themes.{}", theme_id),
            "theme package file is missing".to_string(),
        ));
        return issues;
    };

    let family_id = theme_root_value(&theme_sdn, "family");
    let family_path = theme_section_value(&registry, "families", &family_id);
    if family_id.is_empty() {
        issues.push((
            theme_path.clone(),
            "family".to_string(),
            "theme family is required".to_string(),
        ));
    } else if family_path.is_empty() {
        issues.push((
            "config/themes/theme.sdn".to_string(),
            format!("families.{}", family_id),
            "theme references an unknown family".to_string(),
        ));
    }
    let family_sdn = fs::read_to_string(&family_path).unwrap_or_default();
    for (owner, key, target) in [
        (
            theme_path.as_str(),
            "base_css",
            theme_root_value(&theme_sdn, "base_css"),
        ),
        (
            family_path.as_str(),
            "shape_css",
            theme_root_value(&family_sdn, "shape_css"),
        ),
        (family_path.as_str(), "icons", theme_root_value(&family_sdn, "icons")),
        (
            theme_path.as_str(),
            "source_raw_reference",
            theme_root_value(&theme_sdn, "source_raw_reference"),
        ),
    ] {
        if target.is_empty() {
            issues.push((owner.to_string(), key.to_string(), format!("{} is required", key)));
        } else if !Path::new(&target).exists() {
            issues.push((target, key.to_string(), "referenced file is missing".to_string()));
        }
    }

    let base_path = theme_root_value(&theme_sdn, "base_css");
    let shape_path = theme_root_value(&family_sdn, "shape_css");
    let icons_path = theme_root_value(&family_sdn, "icons");
    let local_widget_dir = theme_root_value(&theme_sdn, "widget_css_dir");
    let family_widget_dir = theme_root_value(&family_sdn, "widget_css_dir");
    let base_css = fs::read_to_string(&base_path).unwrap_or_default();
    let shape_css = fs::read_to_string(&shape_path).unwrap_or_default();
    let icons_sdn = fs::read_to_string(&icons_path).unwrap_or_default();
    let defaults_css = fs::read_to_string(format!("{}/defaults.css", family_widget_dir)).unwrap_or_default();
    let widgets = theme_section_items(&registry, "required_widgets");
    for widget in &widgets {
        let local = format!("{}/{}.css", local_widget_dir, widget);
        let family = format!("{}/{}.css", family_widget_dir, widget);
        let class_name = format!(".widget-{}", widget.replace('_', "-"));
        if !Path::new(&local).exists() && !Path::new(&family).exists() && !defaults_css.contains(&class_name) {
            issues.push((
                "config/themes/theme.sdn".to_string(),
                format!("required_widgets.{}", widget),
                "missing widget CSS in local package or family defaults".to_string(),
            ));
        }
        let local_css = fs::read_to_string(&local).unwrap_or_default();
        if !theme_defined_tokens(&local_css).is_empty() {
            issues.push((
                local,
                widget.clone(),
                "local widget CSS must not define tokens".to_string(),
            ));
        }
    }

    for app in ["Terminal", "Browser", "File Manager", "Editor", "Calculator"] {
        if theme_section_value(&icons_sdn, "apps", app).is_empty() {
            issues.push((
                icons_path.clone(),
                format!("apps.{}", app),
                "missing default app icon".to_string(),
            ));
        }
    }
    for key in [
        "close",
        "minimize",
        "maximize",
        "settings",
        "fallback_app",
        "fallback_file",
    ] {
        if theme_section_value(&icons_sdn, "system", key).is_empty() {
            issues.push((
                icons_path.clone(),
                format!("system.{}", key),
                "missing default system icon".to_string(),
            ));
        }
    }

    for forbidden in ["--ui-", "--app-", "--font-", "--motion-"] {
        if shape_css.contains(forbidden) {
            issues.push((
                shape_path.clone(),
                forbidden.to_string(),
                "family shape CSS must only define shape tokens".to_string(),
            ));
        }
    }
    for forbidden in ["--radius-", "--spacing-", "--blur-", "--border-width-", "--elevation-"] {
        if base_css.contains(forbidden) {
            issues.push((
                base_path.clone(),
                forbidden.to_string(),
                "theme base CSS must not define family shape tokens".to_string(),
            ));
        }
    }

    let tokens = [theme_defined_tokens(&base_css), theme_defined_tokens(&shape_css)].concat();
    theme_validate_refs(&base_path, &base_css, &tokens, &mut issues);
    theme_validate_refs(&shape_path, &shape_css, &tokens, &mut issues);
    theme_validate_refs(&icons_path, &icons_sdn, &tokens, &mut issues);
    theme_validate_refs(
        &format!("{}/defaults.css", family_widget_dir),
        &defaults_css,
        &tokens,
        &mut issues,
    );
    for widget in &widgets {
        for path in [
            format!("{}/{}.css", family_widget_dir, widget),
            format!("{}/{}.css", local_widget_dir, widget),
        ] {
            let css = fs::read_to_string(&path).unwrap_or_default();
            theme_validate_refs(&path, &css, &tokens, &mut issues);
        }
    }
    issues
}

fn lint_theme_package_file(path: &std::path::Path, json_output: bool) -> Option<LintResult> {
    let source = fs::read_to_string(path).unwrap_or_default();
    let issues = validate_theme_package_for_lint();
    let diags: Vec<Diagnostic> = issues
        .into_iter()
        .map(|(issue_path, key, message)| {
            Diagnostic::error(format!("{} {}: {}", issue_path, key, message))
                .with_code("THEME001".to_string())
                .with_file(path.display().to_string())
                .with_label(Span::new(0, 0, 1, 1), "theme package validation")
                .with_help("Fix config/themes/theme.sdn or the referenced theme package file")
        })
        .collect();

    if !json_output {
        if diags.is_empty() {
            println!("{}: OK", path.display());
        } else {
            for diagnostic in &diags {
                println!(
                    "{}:1:1: error: {} [{}]",
                    path.display(),
                    diagnostic.message,
                    diagnostic.code.clone().unwrap_or_else(|| "THEME001".to_string())
                );
                for help in &diagnostic.help {
                    println!("  help: {}", help);
                }
            }
        }
    }

    Some((!diags.is_empty(), diags.len(), 0, diags, Vec::new(), Some(source)))
}

/// Internal lint function that returns diagnostic information
/// Returns: (has_errors, error_count, warning_count, diagnostics, easy_fixes, source_text)
pub fn lint_file_internal(path: &std::path::Path, json_output: bool) -> Option<LintResult> {
    if is_theme_package_lint_path(path) {
        return lint_theme_package_file(path, json_output);
    }

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
                let level_str = if matches!(diagnostic.severity, Severity::Error) {
                    "error"
                } else {
                    "warning"
                };
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
        common_diags
            .iter()
            .filter(|d| matches!(d.severity, Severity::Error))
            .count(),
        common_diags
            .iter()
            .filter(|d| !matches!(d.severity, Severity::Error))
            .count(),
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
