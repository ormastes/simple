//! An omitted argument whose default is a bare name of a `const` bound to a
//! scalar literal is filled with that literal, resolved in the CALLEE's module
//! scope (local, imported, re-exported, glob). Everything else stays rejected.

use simple_parser::ast::{ConstStmt, Expr, Node, Visibility};
use simple_parser::token::Span;
use simple_parser::Parser;

const NOT_CONSTANT: &str = "whose default is not a call-site constant";

fn lower_text(source: &str) -> Result<String, String> {
    let ast = Parser::new(source).parse().expect("parse failed");
    crate::hir::lower(&ast).map(|hir| function_text(&hir, "caller")).map_err(|e| format!("{e}"))
}

fn function_text(hir: &crate::hir::HirModule, name: &str) -> String {
    let function = hir.functions.iter().find(|f| f.name == name).expect("caller function");
    format!("{function:?}")
}

fn marker(name: String) -> Node {
    Node::Const(ConstStmt {
        span: Span::new(0, 0, 0, 0),
        name,
        ty: None,
        value: Expr::Nil,
        visibility: Visibility::Private,
        attributes: vec![],
    })
}

fn binding(importer: &str, local: &str, source_owner: &str, source_name: &str) -> Node {
    marker(format!(
        "{}{}:{importer}{}:{local}{}:{source_owner}{}:{source_name}",
        crate::interpreter::FLATTEN_IMPORT_BINDING_MARKER_PREFIX,
        importer.len(),
        local.len(),
        source_owner.len(),
        source_name.len()
    ))
}

/// `source` as the module loader flattens it: functions carry the owner
/// attribute and every global is preceded by its owner marker.
fn flattened(source: &str, owner: &str) -> Vec<Node> {
    let mut out = Vec::new();
    for mut item in Parser::new(source).parse().expect("parse failed").items {
        match &mut item {
            Node::Function(function) => crate::interpreter::tag_function_module_owner(function, owner),
            Node::Const(_) | Node::Let(_) | Node::Static(_) => out.push(marker(format!(
                "{}{owner}",
                crate::interpreter::FLATTEN_GLOBAL_OWNER_MARKER_PREFIX
            ))),
            _ => {}
        }
        out.push(item);
    }
    out
}

/// Entry module declares its OWN `STATUS` and calls the imported `rejected`
/// with the defaulted argument omitted; `extra` wires the callee's scope.
fn lower_flattened(callee_source: &str, extra: Vec<Node>) -> Result<String, String> {
    let mut module = Parser::new(
        "const STATUS = \"caller_value\"\n\nfn caller() -> text:\n    rejected(\"why\")\n",
    )
    .parse()
    .expect("parse failed");
    module.items.push(binding("<entry>", "rejected", "callee.spl", "rejected"));
    module.items.extend(flattened(callee_source, "callee.spl"));
    module.items.extend(extra);
    crate::hir::lower(&module).map(|hir| function_text(&hir, "caller")).map_err(|e| format!("{e}"))
}

const CALLEE: &str = "fn rejected(reason: text, status: text = STATUS) -> text:\n    status\n";

fn assert_callee_value(result: Result<String, String>, case: &str) {
    let text = result.unwrap_or_else(|e| panic!("{case}: {e}"));
    assert!(text.contains("callee_value"), "{case}: callee's literal must be inlined: {text}");
    assert!(!text.contains("caller_value"), "{case}: caller's same-named const must not be used: {text}");
}

#[test]
fn local_literal_const_default_fills_positional_and_named_calls() {
    let head = "const DFLT = \"blocked\"\nconst COUNT: i64 = 7\n\n\
                fn mk(a: i64, b: i64 = COUNT, c: text = DFLT) -> i64:\n    a + b\n";
    for call in ["mk(1)", "mk(1, 2)", "mk(1, b: 2)", "mk(a: 1)"] {
        let text = lower_text(&format!("{head}fn caller() -> i64:\n    {call}\n")).unwrap_or_else(|e| panic!("{call}: {e}"));
        assert!(text.contains("blocked"), "{call}: literal must be inlined: {text}");
    }
}

#[test]
fn non_constant_identifier_defaults_stay_rejected() {
    let cases = [
        // sibling parameter shadows the const
        "const SIB = \"x\"\nfn mk(SIB: text, c: text = SIB) -> text:\n    c\n",
        // const bound to a call
        "fn f() -> text:\n    \"v\"\nconst NONLIT = f()\nfn mk(a: text, c: text = NONLIT) -> text:\n    c\n",
        // mutable module global
        "var MUT = \"x\"\nfn mk(a: text, c: text = MUT) -> text:\n    c\n",
        // annotation disagrees with the literal's natural type
        "const WIDE: f64 = 1\nfn mk(a: text, c: f64 = WIDE) -> text:\n    a\n",
        // container const
        "const LIST = [1, 2]\nfn mk(a: text, c: [i64] = LIST) -> text:\n    a\n",
        // call default
        "fn f() -> text:\n    \"v\"\nfn mk(a: text, c: text = f()) -> text:\n    c\n",
        // undeclared name
        "fn mk(a: text, c: text = NOWHERE) -> text:\n    c\n",
    ];
    for head in cases {
        let err = lower_text(&format!("{head}fn caller() -> text:\n    mk(\"a\")\n")).expect_err(head);
        assert!(err.contains(NOT_CONSTANT), "{head}: {err}");
    }
}

#[test]
fn imported_const_default_resolves_in_callee_scope() {
    let defs = || flattened("const STATUS = \"callee_value\"\n", "defs.spl");

    // callee declares the const itself
    let own = format!("const STATUS = \"callee_value\"\n\n{CALLEE}");
    assert_callee_value(lower_flattened(&own, vec![]), "callee-local");

    // `use defs.{STATUS}`
    let mut extra = vec![binding("callee.spl", "STATUS", "defs.spl", "STATUS")];
    extra.extend(defs());
    assert_callee_value(lower_flattened(CALLEE, extra), "selective import");

    // `use defs.{STATUS as ...}` under another source name
    let mut extra = vec![binding("callee.spl", "STATUS", "defs.spl", "RAW_STATUS")];
    extra.extend(flattened("const RAW_STATUS = \"callee_value\"\n", "defs.spl"));
    assert_callee_value(lower_flattened(CALLEE, extra), "aliased import");

    // `use facade.{STATUS}` where facade does `export use defs.{STATUS}`
    let mut extra = vec![
        binding("callee.spl", "STATUS", "facade.spl", "STATUS"),
        binding("facade.spl", "STATUS", "defs.spl", "STATUS"),
    ];
    extra.extend(defs());
    assert_callee_value(lower_flattened(CALLEE, extra), "re-export");

    // `use defs.*`
    let mut extra = vec![binding("callee.spl", "*", "defs.spl", "*")];
    extra.extend(defs());
    assert_callee_value(lower_flattened(CALLEE, extra), "glob import");
}

#[test]
fn unresolvable_imported_const_default_stays_rejected() {
    // The callee neither declares nor imports STATUS: the caller's own
    // same-named const must NOT be picked up.
    let err = lower_flattened(CALLEE, vec![]).expect_err("no callee-scope const");
    assert!(err.contains(NOT_CONSTANT), "{err}");

    // Two glob sources both provide it: ambiguous.
    let mut extra = vec![
        binding("callee.spl", "*", "defs.spl", "*"),
        binding("callee.spl", "*", "other.spl", "*"),
    ];
    extra.extend(flattened("const STATUS = \"callee_value\"\n", "defs.spl"));
    extra.extend(flattened("const STATUS = \"other_value\"\n", "other.spl"));
    let err = lower_flattened(CALLEE, extra).expect_err("ambiguous glob");
    assert!(err.contains(NOT_CONSTANT), "{err}");

    // The import names a mutable global, not a literal const.
    let mut extra = vec![binding("callee.spl", "STATUS", "defs.spl", "STATUS")];
    extra.extend(flattened("var STATUS = \"callee_value\"\n", "defs.spl"));
    let err = lower_flattened(CALLEE, extra).expect_err("imported var");
    assert!(err.contains(NOT_CONSTANT), "{err}");
}
