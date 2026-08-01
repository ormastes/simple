//! Verification for the `lenient_types` unresolved-name attribution.
//!
//! These tests pin the *mechanism* described in `lenient_global_diag`: under
//! `lenient_types` an identifier that resolves to nothing becomes
//! `HirExprKind::Global`, which reaches the linker as an undeclared symbol.
//! Before this attribution existed, that happened with no diagnostic of any
//! kind, so a typo surfaced only as a bare symbol name at link time.
//!
//! The two regression cases below are the real blockers that motivated the
//! work:
//!
//! * `interp_list` -- bound by an `if val` pattern that the HIR dispatcher
//!   dropped, so the name was unresolved despite being written correctly.
//! * `animation_time_ms` -- a plain undefined identifier.

use crate::hir::lower::lenient_global_diag::LenientGlobalKind;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::HirExprKind;
use crate::module_resolver::ModuleResolver;
use std::path::Path;

/// Lower `source` in lenient mode with a known file path, returning the
/// lowering output (which carries the attribution index).
///
/// This uses the same constructor as the production lenient entry point
/// (`lower_with_context_lenient`), so `current_file` is populated exactly as it
/// is in the `native_project` per-file lane.
fn lower_lenient_with_file(source: &str, file: &str) -> crate::hir::lower::LoweringOutput {
    let mut parser = simple_parser::Parser::new(source);
    let module = parser.parse().expect("fixture must parse");
    let path = Path::new(file);
    let mut lowerer = Lowerer::with_module_resolver(ModuleResolver::single_file(path), path.to_path_buf());
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    lowerer
        .lower_module_with_warnings(&module)
        .expect("lenient lowering must not fail")
}

/// Every global name referenced anywhere in the lowered module.
fn global_names(output: &crate::hir::lower::LoweringOutput) -> Vec<String> {
    let mut names = Vec::new();
    for func in &output.module.functions {
        for stmt in &func.body {
            collect_stmt_globals(stmt, &mut names);
        }
    }
    names
}

fn collect_stmt_globals(stmt: &crate::hir::types::HirStmt, out: &mut Vec<String>) {
    use crate::hir::types::HirStmt;
    match stmt {
        HirStmt::Expr(e) | HirStmt::Return(Some(e)) => collect_expr_globals(e, out),
        HirStmt::Let {
            value: Some(value), ..
        } => collect_expr_globals(value, out),
        _ => {}
    }
}

fn collect_expr_globals(expr: &crate::hir::types::HirExpr, out: &mut Vec<String>) {
    if let HirExprKind::Global(name) = &expr.kind {
        out.push(name.clone());
    }
    if let HirExprKind::Call { args, .. } = &expr.kind {
        for arg in args {
            collect_expr_globals(arg, out);
        }
    }
}

/// The mechanism itself: an undefined identifier silently becomes a `Global`.
///
/// This is what makes the failure a *link* error rather than a compile error.
/// The test asserts the lowering SUCCEEDS (no error is raised) and that the
/// undefined name is present as a global -- i.e. it will be emitted as an
/// undeclared symbol.
#[test]
fn undefined_identifier_is_lowered_as_a_global_under_lenient_types() {
    let output = lower_lenient_with_file(
        "fn probe() -> i64:\n    return totally_undefined_name\n",
        "/tmp/probe.spl",
    );
    assert!(
        global_names(&output).contains(&"totally_undefined_name".to_string()),
        "expected the undefined name to survive as a Global (that is the link-error mechanism); globals were {:?}",
        global_names(&output)
    );
}

/// The fix: the same lowering now records WHERE the name came from.
#[test]
fn undefined_identifier_is_attributed_to_file_and_function() {
    let output = lower_lenient_with_file(
        "fn probe() -> i64:\n    return totally_undefined_name\n",
        "/tmp/probe.spl",
    );
    let hits = output.lenient_globals.attributions_for("totally_undefined_name");
    assert_eq!(hits.len(), 1, "expected exactly one attribution, got {hits:?}");
    let hit = hits[0];
    assert_eq!(hit.file.as_deref(), Some("/tmp/probe.spl"));
    assert_eq!(hit.function.as_deref(), Some("probe"));
    assert_eq!(hit.kind, LenientGlobalKind::UnresolvedIdentifier);
    assert!(
        hit.function_line.is_some(),
        "attribution must carry a source line"
    );
}

/// A resolvable program must record nothing -- otherwise the count is noise
/// and the population measurement is meaningless.
#[test]
fn fully_resolved_program_records_no_lenient_globals() {
    let output = lower_lenient_with_file(
        "fn probe() -> i64:\n    val x = 1\n    return x\n",
        "/tmp/clean.spl",
    );
    assert!(
        output.lenient_globals.is_empty(),
        "a fully resolved program must produce no attributions, got {:?}",
        output.lenient_globals.entries().collect::<Vec<_>>()
    );
}

/// Regression for the `animation_time_ms` blocker: a plain undefined
/// identifier referenced once inside a function with many parameters, none of
/// which are named that. Previously this reached the linker as a bare symbol.
#[test]
fn animation_time_ms_class_blocker_is_diagnosed_at_its_source() {
    let source = concat!(
        "fn _simple_web_layout_compose_retained(node_id: i64, width: i64, height: i64) -> i64:\n",
        "    return node_id + animation_time_ms\n"
    );
    let output = lower_lenient_with_file(source, "/tmp/web_renderer.spl");
    let hits = output.lenient_globals.attributions_for("animation_time_ms");
    assert_eq!(hits.len(), 1, "expected the undefined param-like name to be attributed");
    assert_eq!(
        hits[0].function.as_deref(),
        Some("_simple_web_layout_compose_retained"),
        "attribution must name the enclosing function, not just the symbol"
    );
    assert_eq!(hits[0].file.as_deref(), Some("/tmp/web_renderer.spl"));
    let rendered = hits[0].format();
    assert!(rendered.contains("animation_time_ms"), "{rendered}");
    assert!(rendered.contains("_simple_web_layout_compose_retained"), "{rendered}");
    assert!(rendered.contains("web_renderer.spl"), "{rendered}");
}

/// Regression for the `interp_list` blocker shape: a name that the author DID
/// bind, but which HIR lowering failed to register, is indistinguishable at
/// this site from a typo -- and both must be attributed rather than silently
/// becoming a link error.
///
/// The `if val` binding bug itself is fixed (`a1c93dd7167`); this pins that
/// *were* such a scope bug to recur, it would now name the function.
#[test]
fn unregistered_binding_class_blocker_is_diagnosed_at_its_source() {
    let source = concat!(
        "fn eval_node(kind: i64) -> i64:\n",
        "    return interp_list\n"
    );
    let output = lower_lenient_with_file(source, "/tmp/interp.spl");
    let hits = output.lenient_globals.attributions_for("interp_list");
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].function.as_deref(), Some("eval_node"));
    assert_eq!(hits[0].file.as_deref(), Some("/tmp/interp.spl"));
}

/// Distinct enclosing functions must be distinct entries, so the population
/// count reflects call sites rather than collapsing to one row per name.
#[test]
fn same_name_in_two_functions_is_two_attributions() {
    let source = concat!(
        "fn first() -> i64:\n",
        "    return shared_missing\n",
        "\n",
        "fn second() -> i64:\n",
        "    return shared_missing\n"
    );
    let output = lower_lenient_with_file(source, "/tmp/two.spl");
    let hits = output.lenient_globals.attributions_for("shared_missing");
    assert_eq!(hits.len(), 2, "got {hits:?}");
}
