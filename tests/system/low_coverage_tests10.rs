//! Low coverage improvement tests - Round 10
//!
//! Targets: settlement/builder.rs, module_resolver.rs, codegen/shared.rs, lexer/mod.rs

// ===========================================================================
// Settlement Builder Tests (simple_loader::settlement)
// ===========================================================================
mod settlement_builder_tests {
    use simple_loader::{find_stub, BuildError, BuildOptions, SettlementBuilder};
    use std::path::PathBuf;

    #[test]
    fn test_build_options_default() {
        let opts = BuildOptions::default();
        assert!(!opts.executable);
        assert!(opts.stub_path.is_none());
        assert!(!opts.debug_info);
        assert_eq!(opts.compression, 0);
    }

    #[test]
    fn test_build_options_current_arch() {
        let arch = BuildOptions::current_arch();
        // Should be non-zero on supported platforms
        #[cfg(target_arch = "x86_64")]
        assert_eq!(arch, 1);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(arch, 2);
        #[cfg(target_arch = "x86")]
        assert_eq!(arch, 3);
    }

    #[test]
    fn test_build_options_executable() {
        let opts = BuildOptions::executable("/path/to/stub");
        assert!(opts.executable);
        assert_eq!(opts.stub_path, Some(PathBuf::from("/path/to/stub")));
    }

    #[test]
    fn test_build_options_settlement_file() {
        let opts = BuildOptions::settlement_file();
        assert!(!opts.executable);
        assert!(opts.stub_path.is_none());
    }

    #[test]
    fn test_settlement_builder_new() {
        let builder = SettlementBuilder::new();
        let _ = builder; // Just test construction
    }

    #[test]
    fn test_settlement_builder_with_options() {
        let opts = BuildOptions::settlement_file();
        let builder = SettlementBuilder::with_options(opts);
        let _ = builder;
    }

    #[test]
    fn test_build_error_io_error() {
        use std::io;
        let io_err = io::Error::new(io::ErrorKind::NotFound, "file not found");
        let err = BuildError::from(io_err);
        match err {
            BuildError::IoError(_) => {}
            _ => panic!("Expected IoError"),
        }
    }

    #[test]
    fn test_build_error_no_entry_point() {
        let err = BuildError::NoEntryPoint;
        assert_eq!(format!("{}", err), "No entry point defined");
    }

    #[test]
    fn test_build_error_invalid_stub() {
        let err = BuildError::InvalidStub;
        assert_eq!(format!("{}", err), "Invalid executable stub");
    }

    #[test]
    fn test_build_error_module_not_found() {
        let err = BuildError::ModuleNotFound("mymodule".to_string());
        assert!(format!("{}", err).contains("mymodule"));
    }

    #[test]
    fn test_find_stub_returns_option() {
        // find_stub looks in several locations, may return None or Some
        let result = find_stub();
        // Just test that it doesn't panic
        let _ = result;
    }
}

// ===========================================================================
// Module Resolver Tests (simple_compiler::ModuleResolver)
// ===========================================================================
mod module_resolver_tests {
    use simple_compiler::{DirectoryManifest, ModuleResolver, ResolvedModule};
    use simple_parser::ast::Visibility;
    use std::path::PathBuf;

    #[test]
    fn test_directory_manifest_default() {
        let manifest = DirectoryManifest::default();
        assert!(manifest.name.is_empty());
        assert!(manifest.attributes.is_empty());
        assert!(manifest.child_modules.is_empty());
        assert!(manifest.common_uses.is_empty());
        assert!(manifest.exports.is_empty());
        assert!(manifest.auto_imports.is_empty());
        assert!(manifest.capabilities.is_empty());
    }

    #[test]
    fn test_directory_manifest_with_name() {
        let mut manifest = DirectoryManifest::default();
        manifest.name = "mymodule".to_string();
        assert_eq!(manifest.name, "mymodule");
    }

    #[test]
    fn test_module_resolver_new() {
        let resolver = ModuleResolver::new(PathBuf::from("/project"), PathBuf::from("/project/src"));
        let _ = resolver;
    }

    #[test]
    fn test_resolved_module_struct() {
        let resolved = ResolvedModule {
            path: PathBuf::from("/project/src/foo.spl"),
            module_path: simple_parser::ast::ModulePath {
                segments: vec!["foo".to_string()],
            },
            is_directory: false,
            manifest: None,
        };
        assert!(!resolved.is_directory);
        assert!(resolved.manifest.is_none());
    }

    #[test]
    fn test_resolved_module_directory() {
        let resolved = ResolvedModule {
            path: PathBuf::from("/project/src/bar/__init__.spl"),
            module_path: simple_parser::ast::ModulePath {
                segments: vec!["bar".to_string()],
            },
            is_directory: true,
            manifest: Some(DirectoryManifest::default()),
        };
        assert!(resolved.is_directory);
        assert!(resolved.manifest.is_some());
    }

    #[test]
    fn test_child_module_struct() {
        use simple_compiler::module_resolver::ChildModule;
        let child = ChildModule {
            name: "submodule".to_string(),
            visibility: Visibility::Public,
            attributes: vec![],
        };
        assert_eq!(child.name, "submodule");
        assert_eq!(child.visibility, Visibility::Public);
    }

    #[test]
    fn test_child_module_private() {
        use simple_compiler::module_resolver::ChildModule;
        let child = ChildModule {
            name: "private_mod".to_string(),
            visibility: Visibility::Private,
            attributes: vec![],
        };
        assert_eq!(child.visibility, Visibility::Private);
    }
}

// ===========================================================================
// Codegen Shared Tests (simple_compiler::codegen::shared)
// ===========================================================================
mod codegen_shared_tests {
    use simple_compiler::codegen::shared::BodyKind;

    #[test]
    fn test_body_kind_actor() {
        let kind = BodyKind::Actor;
        assert_eq!(kind, BodyKind::Actor);
    }

    #[test]
    fn test_body_kind_generator() {
        let kind = BodyKind::Generator;
        assert_eq!(kind, BodyKind::Generator);
    }

    #[test]
    fn test_body_kind_future() {
        let kind = BodyKind::Future;
        assert_eq!(kind, BodyKind::Future);
    }

    #[test]
    fn test_body_kind_equality() {
        assert_eq!(BodyKind::Actor, BodyKind::Actor);
        assert_ne!(BodyKind::Actor, BodyKind::Generator);
        assert_ne!(BodyKind::Generator, BodyKind::Future);
    }

    #[test]
    fn test_body_kind_copy() {
        let kind = BodyKind::Actor;
        let copied = kind; // Copy trait
        assert_eq!(kind, copied);
    }

    #[test]
    fn test_body_kind_clone() {
        let kind = BodyKind::Generator;
        let cloned = kind.clone();
        assert_eq!(kind, cloned);
    }
}

// ===========================================================================
// Lexer Tests (simple_parser::Lexer)
// ===========================================================================
mod lexer_tests {
    use simple_parser::token::TokenKind;
    use simple_parser::Lexer;

    #[test]
    fn test_lexer_new() {
        let lexer = Lexer::new("main = 42");
        let _ = lexer;
    }

    #[test]
    fn test_lexer_tokenize_empty() {
        let mut lexer = Lexer::new("");
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty());
        assert_eq!(tokens.last().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_lexer_tokenize_integer() {
        let mut lexer = Lexer::new("42");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| matches!(t.kind, TokenKind::Integer(_))));
    }

    #[test]
    fn test_lexer_tokenize_identifier() {
        let mut lexer = Lexer::new("foo");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| matches!(t.kind, TokenKind::Identifier(_))));
    }

    #[test]
    fn test_lexer_tokenize_string() {
        let mut lexer = Lexer::new("\"hello\"");
        let tokens = lexer.tokenize();
        // FString is now the default for double-quoted strings
        assert!(tokens
            .iter()
            .any(|t| matches!(t.kind, TokenKind::String(_) | TokenKind::FString(_))));
    }

    #[test]
    fn test_lexer_tokenize_keywords() {
        let mut lexer = Lexer::new("if else while for fn class");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::If));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Else));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::While));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::For));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Fn));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Class));
    }

    #[test]
    fn test_lexer_tokenize_operators() {
        let mut lexer = Lexer::new("+ - * / = == != < > <= >=");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Plus));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Minus));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Star));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Slash));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Assign));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Eq));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::NotEq));
    }

    #[test]
    fn test_lexer_tokenize_brackets() {
        let mut lexer = Lexer::new("( ) [ ] { }");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::LParen));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::RParen));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::LBracket));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::RBracket));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::LBrace));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::RBrace));
    }

    #[test]
    fn test_lexer_tokenize_colon() {
        let mut lexer = Lexer::new(": ::");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Colon));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::DoubleColon));
    }

    #[test]
    fn test_lexer_tokenize_indent_dedent() {
        let mut lexer = Lexer::new("if true:\n    x = 1\ny = 2");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Indent));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Dedent));
    }

    #[test]
    fn test_lexer_tokenize_newline() {
        let mut lexer = Lexer::new("a\nb");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Newline));
    }

    #[test]
    fn test_lexer_tokenize_comment() {
        let mut lexer = Lexer::new("x = 1 # comment\ny = 2");
        let tokens = lexer.tokenize();
        // Comments are skipped, so only x, =, 1, newline, y, =, 2, eof
        assert!(tokens
            .iter()
            .any(|t| matches!(t.kind, TokenKind::Identifier(ref s) if s == "x")));
        assert!(tokens
            .iter()
            .any(|t| matches!(t.kind, TokenKind::Identifier(ref s) if s == "y")));
    }

    #[test]
    fn test_lexer_tokenize_float() {
        let mut lexer = Lexer::new("3.15");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| matches!(t.kind, TokenKind::Float(_))));
    }

    #[test]
    fn test_lexer_tokenize_bool() {
        let mut lexer = Lexer::new("true false");
        let tokens = lexer.tokenize();
        // true/false can be Bool(bool) or True/False keywords
        assert!(tokens
            .iter()
            .any(|t| matches!(t.kind, TokenKind::Bool(true) | TokenKind::True)));
        assert!(tokens
            .iter()
            .any(|t| matches!(t.kind, TokenKind::Bool(false) | TokenKind::False)));
    }

    #[test]
    fn test_lexer_tokenize_nil() {
        let mut lexer = Lexer::new("nil");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Nil));
    }

    #[test]
    fn test_lexer_tokenize_return() {
        let mut lexer = Lexer::new("return 42");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Return));
    }

    #[test]
    fn test_lexer_tokenize_let() {
        let mut lexer = Lexer::new("let x = 1");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Let));
    }

    #[test]
    fn test_lexer_tokenize_async_await() {
        let mut lexer = Lexer::new("async await");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Async));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Await));
    }

    #[test]
    fn test_lexer_tokenize_match_case() {
        let mut lexer = Lexer::new("match case");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Match));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Case));
    }

    #[test]
    fn test_lexer_next_token() {
        let mut lexer = Lexer::new("a b c");
        let t1 = lexer.next_token();
        let t2 = lexer.next_token();
        let t3 = lexer.next_token();
        assert!(matches!(t1.kind, TokenKind::Identifier(_)));
        assert!(matches!(t2.kind, TokenKind::Identifier(_)));
        assert!(matches!(t3.kind, TokenKind::Identifier(_)));
    }

    #[test]
    fn test_lexer_tokenize_arrow() {
        let mut lexer = Lexer::new("-> =>");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Arrow));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::FatArrow));
    }

    #[test]
    fn test_lexer_tokenize_dot() {
        let mut lexer = Lexer::new("a.b");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Dot));
    }

    #[test]
    fn test_lexer_tokenize_comma() {
        let mut lexer = Lexer::new("a, b, c");
        let tokens = lexer.tokenize();
        let comma_count = tokens.iter().filter(|t| t.kind == TokenKind::Comma).count();
        assert_eq!(comma_count, 2);
    }

    #[test]
    fn test_lexer_tokenize_struct_enum() {
        let mut lexer = Lexer::new("struct enum");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Struct));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Enum));
    }

    #[test]
    fn test_lexer_tokenize_trait_impl() {
        let mut lexer = Lexer::new("trait impl");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Trait));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Impl));
    }

    #[test]
    fn test_lexer_tokenize_import_use() {
        let mut lexer = Lexer::new("import use from");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Import));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Use));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::From));
    }

    #[test]
    fn test_lexer_tokenize_pub_mod() {
        let mut lexer = Lexer::new("pub mod");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Pub));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Mod));
    }

    #[test]
    fn test_lexer_tokenize_self_super() {
        let mut lexer = Lexer::new("self super");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Self_));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Super));
    }

    #[test]
    fn test_lexer_tokenize_underscore() {
        let mut lexer = Lexer::new("_ _foo");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Underscore));
    }

    #[test]
    fn test_lexer_tokenize_pipe_ampersand() {
        let mut lexer = Lexer::new("| & || &&");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Pipe));
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Ampersand));
    }

    #[test]
    fn test_lexer_tokenize_at_hash() {
        let mut lexer = Lexer::new("@ #");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::At));
        // # starts a comment, so it's not tokenized
    }

    #[test]
    fn test_lexer_tokenize_question_mark() {
        let mut lexer = Lexer::new("x?");
        let tokens = lexer.tokenize();
        assert!(tokens.iter().any(|t| t.kind == TokenKind::Question));
    }

    #[test]
    fn test_lexer_tokenize_numeric_suffix() {
        let mut lexer = Lexer::new("42i64 3.15f32");
        let tokens = lexer.tokenize();
        assert!(tokens.len() >= 2);
    }
}

// ===========================================================================
// Parser Tests (simple_parser::Parser)
// ===========================================================================
mod parser_tests {
    use simple_parser::Parser;

    #[test]
    fn test_parser_new() {
        let parser = Parser::new("main = 42");
        let _ = parser;
    }

    #[test]
    fn test_parser_parse_empty() {
        let mut parser = Parser::new("");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_simple_assignment() {
        let mut parser = Parser::new("main = 42");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_function() {
        let mut parser = Parser::new("fn foo():\n    return 1");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_class() {
        let mut parser = Parser::new("class Foo:\n    x: i64");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_if() {
        let mut parser = Parser::new("if true:\n    x = 1");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_while() {
        let mut parser = Parser::new("while true:\n    x = 1");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_for() {
        let mut parser = Parser::new("for i in items:\n    print(i)");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_match() {
        let mut parser = Parser::new("match x:\n    case 1:\n        y = 1");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_struct() {
        let mut parser = Parser::new("struct Point:\n    x: i64\n    y: i64");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_enum() {
        let mut parser = Parser::new("enum Color:\n    Red\n    Green\n    Blue");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_trait() {
        let mut parser = Parser::new("trait Printable:\n    fn print(self)");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_import() {
        let mut parser = Parser::new("import foo");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_use() {
        let mut parser = Parser::new("use foo.bar");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_binary_expr() {
        let mut parser = Parser::new("x = 1 + 2 * 3");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_call() {
        let mut parser = Parser::new("foo(1, 2, 3)");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_method_call() {
        let mut parser = Parser::new("obj.method()");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_array_literal() {
        let mut parser = Parser::new("arr = [1, 2, 3]");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_dict_literal() {
        let mut parser = Parser::new("d = {a: 1, b: 2}");
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parser_parse_lambda() {
        let mut parser = Parser::new("f = |x| x + 1");
        let result = parser.parse();
        assert!(result.is_ok());
    }
}
