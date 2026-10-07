//! Root imports must retain the provider selected by the flattened loader.
use simple_compiler::interpreter;
use simple_parser::{Parser, ast::{Attribute, Node}};

fn binding(importer: &str, local: &str, owner: &str, original: &str) -> Node {
    let mut module = Parser::new("const marker = 0\n").parse().unwrap();
    let Node::Const(ref mut value) = module.items[0] else { panic!("const marker"); };
    value.name = format!("__simple_flatten_import_binding__={}:{}{}:{}{}:{}{}:{}",
        importer.len(), importer, local.len(), local, owner.len(), owner, original.len(), original);
    module.items.remove(0)
}

fn provider(owner: &str, result: i32) -> Node {
    let source = format!("fn selected(value: i64) -> i64:\n    {result}\n");
    let mut module = Parser::new(&source).parse().unwrap();
    let Node::Function(ref mut function) = module.items[0] else { panic!("provider function"); };
    function.attributes.push(Attribute {
        span: function.span, name: format!("__simple_flatten_module_owner__={owner}"),
        value: None, args: None, named_args: None,
    });
    module.items.remove(0)
}

fn run(facade: bool) -> i32 {
    let root = tempfile::tempdir().unwrap();
    let wrong = root.path().join("wrong.spl").to_string_lossy().into_owned();
    let wanted = root.path().join("wanted.spl").to_string_lossy().into_owned();
    let reexport = root.path().join("facade.spl").to_string_lossy().into_owned();
    let mut items = vec![provider(&wrong, 22), provider(&wanted, 11)];
    items.push(binding("<entry>", "selected", if facade { &reexport } else { &wanted }, "selected"));
    if facade { items.push(binding(&reexport, "selected", &wanted, "selected")); }
    items.extend(Parser::new("main = selected(7)\n").parse().unwrap().items);
    interpreter::evaluate_module(&items).unwrap()
}

#[test]
fn root_selective_import_uses_bound_provider() { assert_eq!(run(false), 11); }

#[test]
fn root_reexport_import_uses_bound_provider() { assert_eq!(run(true), 11); }
