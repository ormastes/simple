use simple_parser::ast::Node;
use simple_parser::Parser;

#[test]
fn parse_gc_module_attribute_before_export_only_root() {
    let source = r#"
@gc

export GpuDevice
export gpu_init, gpu_sync
"#;
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse @gc before export-only module root");

    assert_eq!(module.items.len(), 2);
    assert!(matches!(module.items[0], Node::ExportUseStmt(_)));
    assert!(matches!(module.items[1], Node::ExportUseStmt(_)));
}
