use simple_parser::{Parser, ast::Node};

#[test]
fn test_parse_mixin_declaration() {
    let source = r#"mixin Timestamp:
    created_at: i64
    updated_at: i64
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    
    assert!(result.is_ok(), "Failed to parse mixin: {:?}", result.err());
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Mixin(mixin) = &module.items[0] {
        assert_eq!(mixin.name, "Timestamp");
        assert_eq!(mixin.fields.len(), 2);
        assert_eq!(mixin.fields[0].name, "created_at");
        assert_eq!(mixin.fields[1].name, "updated_at");
    } else {
        panic!("Expected Mixin node, got {:?}", module.items[0]);
    }
}

#[test]
fn test_parse_class_with_mixin() {
    let source = r#"mixin Timestamp:
    created_at: i64

class User:
    use Timestamp
    id: i64
    name: String
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    let module = result.unwrap();
    assert_eq!(module.items.len(), 2);
    
    if let Node::Class(class) = &module.items[1] {
        assert_eq!(class.name, "User");
        assert_eq!(class.mixins.len(), 1);
        assert_eq!(class.mixins[0].name, "Timestamp");
        assert_eq!(class.fields.len(), 2);
    } else {
        panic!("Expected Class node, got {:?}", module.items[1]);
    }
}
