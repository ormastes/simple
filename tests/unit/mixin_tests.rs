//! Unit tests for mixin functionality
//! Tests parsing, type checking, and HIR lowering of mixins

#[cfg(test)]
mod mixin_parser_tests {
    use simple_parser::{Parser, TokenStream};
    use simple_lexer::Lexer;

    #[test]
    fn test_parse_simple_mixin() {
        let source = r#"
mixin Timestamp
    created_at: i64
    updated_at: i64
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse simple mixin: {:?}", result.err());
    }

    #[test]
    fn test_parse_mixin_with_methods() {
        let source = r#"
mixin Auditable
    modified_by: str
    
    fn mark_modified(user: str)
        self.modified_by = user
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse mixin with methods: {:?}", result.err());
    }

    #[test]
    fn test_parse_generic_mixin() {
        let source = r#"
mixin Serializable<T>
    fn to_json() -> str
        return "{}"
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse generic mixin: {:?}", result.err());
    }

    #[test]
    fn test_parse_mixin_with_trait_bounds() {
        let source = r#"
mixin Comparable<T> where T: Ord
    fn compare(other: T) -> i32
        return 0
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse mixin with trait bounds: {:?}", result.err());
    }

    #[test]
    fn test_parse_class_with_mixin() {
        let source = r#"
mixin Timestamp
    created_at: i64

class User
    use Timestamp
    id: i64
    name: str
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse class with mixin: {:?}", result.err());
    }

    #[test]
    fn test_parse_class_with_multiple_mixins() {
        let source = r#"
mixin Timestamp
    created_at: i64

mixin Auditable
    modified_by: str

class Document
    use Timestamp
    use Auditable
    content: str
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse class with multiple mixins: {:?}", result.err());
    }

    #[test]
    fn test_parse_class_with_generic_mixin() {
        let source = r#"
mixin Serializable<T>
    fn to_json() -> str
        return "{}"

class Product
    use Serializable<Product>
    id: i64
"#;
        let lexer = Lexer::new(source);
        let tokens: Vec<_> = lexer.collect();
        let mut parser = Parser::new(TokenStream::new(tokens));
        
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse class with generic mixin: {:?}", result.err());
    }
}

#[cfg(test)]
mod mixin_type_tests {
    use simple_type::{Type, MixinType};

    #[test]
    fn test_mixin_type_creation() {
        let mixin = MixinType::new(
            "Timestamp".to_string(),
            vec![],
            vec![
                ("created_at".to_string(), Type::I64),
                ("updated_at".to_string(), Type::I64),
            ],
            vec![],
            vec![],
        );

        assert_eq!(mixin.name(), "Timestamp");
        assert_eq!(mixin.fields().len(), 2);
        assert_eq!(mixin.type_params().len(), 0);
    }

    #[test]
    fn test_generic_mixin_type() {
        let mixin = MixinType::new(
            "Serializable".to_string(),
            vec!["T".to_string()],
            vec![],
            vec![],
            vec![],
        );

        assert_eq!(mixin.name(), "Serializable");
        assert_eq!(mixin.type_params().len(), 1);
        assert_eq!(mixin.type_params()[0], "T");
    }

    #[test]
    fn test_mixin_type_substitution() {
        let mixin = MixinType::new(
            "Container".to_string(),
            vec!["T".to_string()],
            vec![
                ("value".to_string(), Type::Var("T".to_string())),
            ],
            vec![],
            vec![],
        );

        let mut subst = std::collections::HashMap::new();
        subst.insert("T".to_string(), Type::I64);

        let substituted = mixin.apply_substitution(&subst);
        
        assert_eq!(substituted.fields()[0].1, Type::I64);
    }
}

#[cfg(test)]
mod mixin_integration_tests {
    // These tests would require the full compiler pipeline
    // For now, we'll skip them until the compiler builds successfully

    #[test]
    #[ignore = "Requires full compiler build"]
    fn test_mixin_hir_lowering() {
        // TODO: Test HIR lowering once compiler builds
    }

    #[test]
    #[ignore = "Requires full compiler build"]
    fn test_mixin_field_expansion() {
        // TODO: Test that mixin fields are expanded into class
    }

    #[test]
    #[ignore = "Requires full compiler build"]
    fn test_mixin_method_lowering() {
        // TODO: Test that mixin methods are lowered correctly
    }
}
