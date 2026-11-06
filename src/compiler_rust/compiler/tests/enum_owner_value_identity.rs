//! Same-named enum declarations need identity after values leave their owner.
use simple_compiler::interpreter;
use simple_parser::{ast::{Attribute, Node}, Parser};

fn owner_nodes(source: &str, owner: &str) -> Vec<Node> {
    let mut module = Parser::new(source).parse().expect("owner fixture parses");
    for item in &mut module.items {
        match item {
            Node::Enum(def) => def.attributes.push(Attribute {
                span: def.span,
                name: format!("__simple_flatten_module_owner__={owner}"),
                value: None,
                args: None,
                named_args: None,
            }),
            Node::Function(def) => def.attributes.push(Attribute {
                span: def.span,
                name: format!("__simple_flatten_module_owner__={owner}"),
                value: None,
                args: None,
                named_args: None,
            }),
            _ => {}
        }
    }
    module.items
}

fn run(body: &str) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let root = tempfile::tempdir().expect("owner paths");
    let a = root.path().join("a.spl").to_string_lossy().into_owned();
    let b = root.path().join("b.spl").to_string_lossy().into_owned();
    let mut items = owner_nodes(
        "enum Mode:\n    Alpha\n    Shared\n    Payload(value: i64)\n\nfn a_shared() -> Mode:\n    Mode.Shared\n\nfn a_payload() -> Mode:\n    Mode.Payload(7)\n\nfn a_other() -> Mode:\n    Mode.Alpha\n",
        &a,
    );
    items.extend(owner_nodes(
        "enum Mode:\n    Beta\n    Shared\n    Payload(value: i64)\n\nfn b_shared() -> Mode:\n    Mode.Shared\n\nfn b_payload() -> Mode:\n    Mode.Payload(7)\n",
        &b,
    ));
    let tail = format!("fn main() -> i64:\n{body}\nmain = main()\n");
    items.extend(Parser::new(&tail).parse().expect("consumer fixture parses").items);
    interpreter::evaluate_module(&items).expect("consumer fixture executes")
}

#[test]
fn same_owner_enum_value_equality_is_preserved() {
    assert_eq!(run("    if a_shared() != a_shared(): return 1\n    if a_shared() == a_other(): return 2\n    if a_payload() != a_payload(): return 3\n    return 0"), 0);
}

#[test]
fn same_named_unit_variants_from_different_owners_are_not_equal() {
    assert_eq!(run("    if a_shared() == b_shared(): return 1\n    return 0"), 0,
        "module-aware definition selection must survive unit-value construction");
}

#[test]
fn same_named_payload_variants_from_different_owners_are_not_equal() {
    assert_eq!(run("    if a_payload() == b_payload(): return 1\n    return 0"), 0,
        "matching variant/payload contents do not erase the declaring enum identity");
}
