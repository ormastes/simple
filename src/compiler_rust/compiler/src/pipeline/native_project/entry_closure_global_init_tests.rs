//! Regression tests for defect C1 (entry-closure freestanding codegen defect
//! catalog, doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md):
//! module-global `val/var X = call()` initializers never emitted under
//! `--entry-closure` freestanding native-build.
//!
//! Root cause isolated here (not the doc's originally-cited repro -- see
//! below): `wrap_entry_script_as_main` (compiler.rs) runs on every
//! `--entry` `.spl` file that has no function literally named `main`.
//! Freestanding OS entry files commonly define their own boot entry point
//! (`fn spl_start():`) instead of `main`, so `has_explicit_main` returns
//! false and the transform still fires. Before this fix it moved *every*
//! top-level `val`/`var`/`const`/`static` declaration whose initializer is
//! not compile-time-constant (e.g. a call) into the body of a *synthetic*
//! `main` function. Under freestanding/entry-closure builds that synthetic
//! `main` is dead code (the real entry point is `spl_start`/`_start`, never
//! `main` -- see crt0.s), so the declaration was not just missing its
//! runtime init side effect: `module_pass.rs` only scans *top-level*
//! `module.items` for global registration, so a declaration buried inside
//! `main`'s body is not registered as a global AT ALL. Any other top-level
//! function in the same file referencing that name compiles to a dangling
//! `GlobalLoad`/`GlobalStore` against a symbol nothing defines.
//!
//! Confirmed empirically (2026-07-17, seed native-build,
//! `--entry-closure --target x86_64-unknown-none --backend cranelift`) with
//! a 2-file repro (entry file defining `spl_start()` + a top-level
//! `var h = local_make()` read from `spl_start`): before this fix, the link
//! step failed with `undefined symbol: entry_kernel__h_entry_thing`
//! referenced from `entry_kernel__spl_start`. A sibling *library* module's
//! call-initialized global (the doc's originally-cited
//! `_browser_default_font_lock` shape) was already correctly handled by the
//! separate `inject_freestanding_module_global_init` + linker
//! `generate_init_caller` + crt0.s `__simple_call_module_inits` call chain
//! (landed 2026-07-17 01:13 UTC, before this fix) -- that mechanism is
//! unaffected by this file; these tests exercise the entry-file-specific gap
//! that mechanism could not reach because `wrap_entry_script_as_main` had
//! already erased the declaration from `module.items` before injection ran.

use simple_parser::ast::Node;
use simple_parser::Pattern;

fn parse(source: &str) -> simple_parser::ast::Module {
    simple_parser::Parser::new(source)
        .parse()
        .unwrap_or_else(|e| panic!("parse failed: {e}\nsource:\n{source}"))
}

fn pattern_name(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => Some(name.clone()),
        Pattern::Typed { pattern, .. } => pattern_name(pattern),
        _ => None,
    }
}

fn top_level_let_names(module: &simple_parser::ast::Module) -> Vec<String> {
    module
        .items
        .iter()
        .filter_map(|item| match item {
            Node::Let(l) => pattern_name(&l.pattern),
            _ => None,
        })
        .collect()
}

fn has_top_level_function(module: &simple_parser::ast::Module, name: &str) -> bool {
    module
        .items
        .iter()
        .any(|item| matches!(item, Node::Function(f) if f.name == name))
}

/// Entry file with no explicit `main`, defining its own `spl_start` boot
/// entry point, one call-initialized global (`h_entry_thing`), and one
/// const-initialized global (`i_const_read`) -- both read from `spl_start`.
/// This is the minimal shape of the confirmed link-failure repro.
const ENTRY_SOURCE: &str = "\
fn local_make() -> i64:
    return 7

var h_entry_thing: i64 = local_make()

var i_const_read: bool = true

fn spl_start():
    val b = h_entry_thing
    val c = i_const_read
";

#[test]
fn freestanding_entry_keeps_call_initialized_global_at_module_scope() {
    let module = parse(ENTRY_SOURCE);
    let wrapped = super::compiler::wrap_entry_script_as_main(module, /* is_freestanding */ true);

    // Before the fix: `h_entry_thing` (non-const initializer) was buried
    // inside a synthesized `main` and vanished from `module.items` --
    // `module_pass.rs` never registered it as a global, producing the
    // `undefined symbol: entry_kernel__h_entry_thing` link failure this test
    // guards against.
    let names = top_level_let_names(&wrapped);
    assert!(
        names.contains(&"h_entry_thing".to_string()),
        "call-initialized global must stay at module scope under freestanding \
         entry-closure builds so it is registered as a real global and so \
         `inject_freestanding_module_global_init` (which runs right after this \
         transform) can see it and synthesize its runtime init; got top-level \
         let names: {:?}",
        names
    );
    assert!(
        names.contains(&"i_const_read".to_string()),
        "const-initialized global must also stay at module scope; got: {:?}",
        names
    );

    // `spl_start` -- the real freestanding boot entry -- must survive
    // untouched as its own top-level function.
    assert!(has_top_level_function(&wrapped, "spl_start"));
}

/// A hosted script entry whose only reader of the call-initialized binding is
/// the top-level script body itself. Nothing outside the synthesized `main`
/// needs the name, so it must stay a local of `main` -- that is what keeps a
/// script's statement order (including the initializer's side effects)
/// exactly as written.
const HOSTED_SCRIPT_ONLY_SOURCE: &str = "\
fn h() -> i64:
    return 7

print(\"A\")

var script_local: i64 = h()

print(script_local)
";

#[test]
fn hosted_entry_buries_declarations_read_only_by_the_script_body() {
    // Regression guard for script *ordering*: a binding nothing outside the
    // script body reads has no reason to become a module global, and lifting
    // it would hoist its initializer's side effects ahead of the script
    // statements that precede it (here, ahead of `print("A")`).
    let module = parse(HOSTED_SCRIPT_ONLY_SOURCE);
    let wrapped = super::compiler::wrap_entry_script_as_main(module, /* is_freestanding */ false);

    let names = top_level_let_names(&wrapped);
    assert!(
        !names.contains(&"script_local".to_string()),
        "a call-initialized binding read only by the script body must stay \
         buried in the synthetic `main` so script statement order is \
         preserved; got top-level let names: {:?}",
        names
    );
    assert!(
        has_top_level_function(&wrapped, "main"),
        "hosted entry with no explicit main must still get a synthesized main"
    );
}

#[test]
fn hosted_entry_lifts_call_initialized_global_read_by_a_sibling_function() {
    // The declaration is read by `spl_start`, which stays a *sibling* of the
    // synthesized `main`. Burying the declaration inside `main` makes it a
    // local of `main`, so the sibling has nothing to resolve against: under
    // `compile` that is `Undefined("undefined identifier: h_entry_thing")`,
    // and under `native-build` there is no diagnostic at all -- the sibling
    // silently reads an uninitialized global (observed printing
    // 216172782176749384 instead of 7). Lifting it restores a real
    // module-scope global, which `module_pass` then registers and initializes
    // via `__module_init_dynamic`.
    //
    // This assertion replaces an earlier one that required the opposite. That
    // one was written when only the freestanding half of this defect was
    // understood, and it pinned the hosted half of the same bug in place.
    let module = parse(ENTRY_SOURCE);
    let wrapped = super::compiler::wrap_entry_script_as_main(module, /* is_freestanding */ false);

    let names = top_level_let_names(&wrapped);
    assert!(
        names.contains(&"h_entry_thing".to_string()),
        "a call-initialized global read by a sibling top-level function must \
         stay at module scope even for hosted entries; got top-level let \
         names: {:?}",
        names
    );
    // Const-initialized declarations were already lifted unconditionally
    // (pre-existing `is_liftable_global_decl` behavior) -- unaffected by
    // this fix, verified here as a no-regression check.
    assert!(
        names.contains(&"i_const_read".to_string()),
        "const-initialized global stays lifted regardless of target; got: {:?}",
        names
    );

    assert!(has_top_level_function(&wrapped, "spl_start"));

    // ENTRY_SOURCE has no top-level statements other than the two
    // declarations, so once both are lifted the script body is empty and no
    // `main` is synthesized -- the same outcome a pure-declaration entry file
    // (only functions and const globals) already produced before this change.
    // Verified equivalent on real builds: hosted `native-build` of this shape
    // links and runs clean both before and after, printing nothing either way,
    // because `spl_start` is not an entry point on a hosted target. The
    // "script statements still get a synthesized main" guarantee is covered by
    // `hosted_entry_buries_declarations_read_only_by_the_script_body`, which
    // has a real script body.
    assert!(
        !has_top_level_function(&wrapped, "main"),
        "an entry file whose script body is empty after lifting must not gain \
         a synthesized `main`; got top-level items: {:?}",
        wrapped.items.iter().map(node_kind).collect::<Vec<_>>()
    );
}

#[test]
fn hosted_entry_lifts_global_read_by_a_class_method() {
    // Class/impl methods are siblings of the synthesized `main` too, and they
    // reach the free-read scan only as bare `FunctionDef`s -- never as a
    // `Node::Function` -- so they need their own walk. Without it this case
    // would silently keep the pre-fix (broken) behavior.
    let source = "\
fn make() -> i64:
    return 7

var seen_by_method: i64 = make()

class Reader:
    fn read(self) -> i64:
        return seen_by_method

print(1)
";
    let module = parse(source);
    let wrapped = super::compiler::wrap_entry_script_as_main(module, /* is_freestanding */ false);
    let names = top_level_let_names(&wrapped);
    assert!(
        names.contains(&"seen_by_method".to_string()),
        "a global read from a class method must stay at module scope; got: {:?}",
        names
    );
}

#[test]
fn explicit_main_short_circuits_regardless_of_freestanding_flag() {
    let source = "\
fn main():
    val x = 1
";
    let module = parse(source);
    let wrapped_freestanding = super::compiler::wrap_entry_script_as_main(module.clone(), true);
    let wrapped_hosted = super::compiler::wrap_entry_script_as_main(module, false);
    assert_eq!(wrapped_freestanding.items.len(), wrapped_hosted.items.len());
    assert!(has_top_level_function(&wrapped_freestanding, "main"));
    assert_eq!(wrapped_freestanding.items.len(), 1);
}

/// Closes the gap flagged in review: link success alone does not prove the
/// call-initialized global's value actually gets computed at runtime -- only
/// that the linker found a (possibly zero-initialized, never-written) `.data`
/// slot for it. This chains the two real passes exactly as
/// `compile_file_to_object` does (`wrap_entry_script_as_main` then
/// `inject_freestanding_module_global_init`) and asserts the synthesized
/// `__module_init_entry_kernel_dynamic` function exists AND contains a real
/// assignment to `h_entry_thing` -- i.e. the runtime-init call chain
/// (crt0.s -> `__simple_call_module_inits` -> this function, confirmed
/// present and wired in crt0.s separately) has something real to call.
#[test]
fn freestanding_entry_call_initializer_gets_a_runtime_init_assignment() {
    let module = parse(ENTRY_SOURCE);
    let mut wrapped = super::compiler::wrap_entry_script_as_main(module, /* is_freestanding */ true);
    super::module_global_init::inject_freestanding_module_global_init(&mut wrapped, "entry_kernel");

    let init_fn = wrapped
        .items
        .iter()
        .find_map(|item| match item {
            Node::Function(f) if f.name.starts_with("__module_init_") => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "expected a synthesized __module_init_* function for the \
                 call-initialized global `h_entry_thing`; got top-level items: {:?}",
                wrapped.items.iter().map(node_kind).collect::<Vec<_>>()
            )
        });
    assert_eq!(init_fn.name, "__module_init_entry_kernel_dynamic");

    let assigns_h_entry_thing = init_fn.body.statements.iter().any(|stmt| {
        matches!(
            stmt,
            Node::Assignment(simple_parser::ast::AssignmentStmt {
                target: simple_parser::ast::Expr::Identifier(name),
                ..
            }) if name == "h_entry_thing"
        )
    });
    assert!(
        assigns_h_entry_thing,
        "synthesized init function must assign h_entry_thing = local_make(); got statements: {:?}",
        init_fn.body.statements
    );

    // `i_const_read` is const-foldable and already captured as static .data
    // metadata by module_pass.rs -- it must NOT get a redundant runtime
    // assignment here (that would just be extra dead work, not a bug, but
    // asserting its absence pins down that the two initialization paths
    // (static metadata vs. runtime-init) stay partitioned as designed).
    let assigns_i_const_read = init_fn.body.statements.iter().any(|stmt| {
        matches!(
            stmt,
            Node::Assignment(simple_parser::ast::AssignmentStmt {
                target: simple_parser::ast::Expr::Identifier(name),
                ..
            }) if name == "i_const_read"
        )
    });
    assert!(!assigns_i_const_read);
}

fn node_kind(node: &Node) -> &'static str {
    match node {
        Node::Let(_) => "Let",
        Node::Const(_) => "Const",
        Node::Static(_) => "Static",
        Node::Function(_) => "Function",
        _ => "other",
    }
}
