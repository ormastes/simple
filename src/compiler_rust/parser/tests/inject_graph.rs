use simple_parser::ast::*;
use simple_parser::Parser;

fn parse_one(source: &str) -> Node {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse inject graph");
    assert_eq!(module.items.len(), 1);
    module.items.into_iter().next().unwrap()
}

#[test]
fn parses_compile_inject_graph_with_defaults() {
    let source = r#"inject AppGraph compile:
    root App
    scan app.*
    scan infra.*
    bind UserRepo = SqlUserRepo lifetime scoped configurable
    bind CryptoRng = SystemCryptoRng lifetime singleton final
"#;

    let node = parse_one(source);
    let Node::InjectGraph(graph) = node else {
        panic!("expected InjectGraph");
    };

    assert_eq!(graph.name, "AppGraph");
    assert_eq!(graph.mode, Some(InjectMode::Compile));
    assert_eq!(graph.items.len(), 5);

    assert!(matches!(&graph.items[0], InjectItem::Root { type_ref, .. } if type_ref == "App"));
    assert!(matches!(&graph.items[1], InjectItem::Scan { pattern, .. } if pattern == "app.*"));
    assert!(matches!(
        &graph.items[3],
        InjectItem::Bind {
            service,
            target,
            lifetime: Some(InjectLifetime::Scoped),
            configurable: true,
            final_binding: false,
            ..
        } if service == "UserRepo" && target == "SqlUserRepo"
    ));
    assert!(matches!(
        &graph.items[4],
        InjectItem::Bind {
            service,
            target,
            lifetime: Some(InjectLifetime::Singleton),
            configurable: false,
            final_binding: true,
            ..
        } if service == "CryptoRng" && target == "SystemCryptoRng"
    ));
}

#[test]
fn parses_mixed_inject_graph_runtime_slot_and_profile() {
    let source = r#"inject AgentGraph mixed:
    root Agent
    load "config/di.sdn"
    slot [ToolPlugin] runtime named plugins default GrepPlugin
    profile test:
        bind UserRepo = MemoryUserRepo
"#;

    let node = parse_one(source);
    let Node::InjectGraph(graph) = node else {
        panic!("expected InjectGraph");
    };

    assert_eq!(graph.name, "AgentGraph");
    assert_eq!(graph.mode, Some(InjectMode::Mixed));
    assert!(matches!(&graph.items[1], InjectItem::Load { path, .. } if path == "config/di.sdn"));
    assert!(matches!(
        &graph.items[2],
        InjectItem::Slot {
            service,
            qualifier: Some(qualifier),
            default_target: Some(default_target),
            ..
        } if service == "[ToolPlugin]" && qualifier == "plugins" && default_target == "GrepPlugin"
    ));
    assert!(matches!(&graph.items[3], InjectItem::Profile { name, items, .. } if name == "test" && items.len() == 1));
}

#[test]
fn inject_remains_available_as_expression_identifier() {
    let mut parser = Parser::new("val app = inject\n");
    let module = parser.parse().expect("inject identifier expression should parse");
    assert!(matches!(&module.items[0], Node::Let(_)));
}
