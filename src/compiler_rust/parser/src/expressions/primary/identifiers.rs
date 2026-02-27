use crate::ast::Expr;
use crate::error::ParseError;
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_identifier(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Result => {
                // Allow 'result' as a regular identifier (like 'type', 'out', etc.)
                // ContractResult expression is only generated in contract blocks
                self.advance();
                Ok(Expr::Identifier("result".to_string()))
            }
            TokenKind::Identifier { name, .. } => self.parse_identifier_or_struct(name),
            TokenKind::Self_ => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
            TokenKind::Super => {
                self.advance();
                Ok(Expr::Identifier("super".to_string()))
            }
            TokenKind::Out => {
                self.advance();
                Ok(Expr::Identifier("out".to_string()))
            }
            TokenKind::OutErr => {
                self.advance();
                Ok(Expr::Identifier("out_err".to_string()))
            }
            TokenKind::Type => {
                self.advance();
                Ok(Expr::Identifier("type".to_string()))
            }
            TokenKind::Feature => self.parse_keyword_identifier("feature"),
            TokenKind::Scenario => self.parse_keyword_identifier("scenario"),
            TokenKind::Outline => self.parse_keyword_identifier("outline"),
            TokenKind::Examples => self.parse_keyword_identifier("examples"),
            TokenKind::Given => self.parse_keyword_identifier("given"),
            TokenKind::When => self.parse_keyword_identifier("when"),
            TokenKind::Then => self.parse_keyword_identifier("then"),
            TokenKind::AndThen => self.parse_keyword_identifier("and_then"),
            TokenKind::Context => self.parse_keyword_identifier("context"),
            TokenKind::Common => self.parse_keyword_identifier("common"),
            // Allow math keywords to be used as identifiers outside m{} blocks
            TokenKind::Slice => self.parse_keyword_identifier("Slice"),
            TokenKind::Flat => self.parse_keyword_identifier("Flat"),
            TokenKind::Vec => self.parse_vec_keyword(),
            TokenKind::Gpu => {
                self.advance();
                Ok(Expr::Identifier("gpu".to_string()))
            }
            // Allow 'alias' to be used as identifier (e.g., `with resource as alias: captured = alias`)
            // The 'alias' keyword is only used in type aliasing context: `alias NewType = OldType`
            TokenKind::Alias => self.parse_keyword_identifier("alias"),
            // Allow 'bounds' to be used as identifier (variable name)
            // The 'bounds' keyword is only used in type constraint contexts
            TokenKind::Bounds => self.parse_keyword_identifier("bounds"),
            TokenKind::Default => self.parse_keyword_identifier("default"),
            // Allow 'new' and 'old' to be used as identifiers (variable names)
            // These are keywords only in specific contexts: new Type(...) and old(x)
            TokenKind::New => self.parse_keyword_identifier("new"),
            TokenKind::Old => self.parse_keyword_identifier("old"),
            // Allow 'from' and 'to' to be used as identifiers (variable names)
            // These are keywords only in specific contexts: from keyword in imports, to in ranges
            TokenKind::From => self.parse_keyword_identifier("from"),
            TokenKind::To => self.parse_keyword_identifier("to"),
            // Allow various keywords to be used as identifiers in expression contexts
            // Simple uses these as variable/parameter names in source files
            TokenKind::Loop => self.parse_keyword_identifier("loop"),
            TokenKind::Unit => self.parse_keyword_identifier("Unit"),
            TokenKind::Sync => self.parse_keyword_identifier("sync"),
            TokenKind::Async => self.parse_keyword_identifier("async"),
            TokenKind::Kernel => self.parse_keyword_identifier("kernel"),
            TokenKind::Val => self.parse_keyword_identifier("val"),
            TokenKind::Literal => self.parse_keyword_identifier("literal"),
            TokenKind::As => self.parse_keyword_identifier("as"),
            TokenKind::Repr => self.parse_keyword_identifier("repr"),
            TokenKind::Extern => self.parse_keyword_identifier("extern"),
            TokenKind::Static => self.parse_keyword_identifier("static"),
            TokenKind::Const => self.parse_keyword_identifier("const"),
            TokenKind::Shared => self.parse_keyword_identifier("Shared"),
            TokenKind::Dyn => self.parse_keyword_identifier("dyn"),
            TokenKind::Macro => self.parse_keyword_identifier("macro"),
            TokenKind::Mixin => self.parse_keyword_identifier("mixin"),
            TokenKind::Actor => self.parse_keyword_identifier("actor"),
            TokenKind::Ghost => self.parse_keyword_identifier("ghost"),
            TokenKind::Gen => self.parse_keyword_identifier("gen"),
            TokenKind::Impl => self.parse_keyword_identifier("impl"),
            TokenKind::Exists => self.parse_keyword_identifier("exists"),
            TokenKind::Match => self.parse_keyword_identifier("match"),
            TokenKind::Asm => self.parse_keyword_identifier("asm"),
            TokenKind::Bitfield => self.parse_keyword_identifier("bitfield"),
            TokenKind::Newtype => self.parse_keyword_identifier("newtype"),
            TokenKind::Extend => self.parse_keyword_identifier("extend"),
            TokenKind::Comptime => self.parse_keyword_identifier("comptime"),
            // Type definition keywords usable as identifiers in expression contexts
            TokenKind::Struct => self.parse_keyword_identifier("struct"),
            TokenKind::Enum => self.parse_keyword_identifier("enum"),
            TokenKind::Class => self.parse_keyword_identifier("class"),
            TokenKind::Fn => self.parse_keyword_identifier("fn"),
            TokenKind::Trait => self.parse_keyword_identifier("trait"),
            // Allow operator keywords as identifiers (e.g., xor(a, b), or(a, b) function calls)
            TokenKind::Xor => self.parse_keyword_identifier("xor"),
            TokenKind::Or => self.parse_keyword_identifier("or"),
            TokenKind::And => self.parse_keyword_identifier("and"),
            TokenKind::Not => self.parse_keyword_identifier("not"),
            TokenKind::In => self.parse_keyword_identifier("in"),
            TokenKind::Is => self.parse_keyword_identifier("is"),
            // Allow 'tensor' and 'union' as identifiers
            TokenKind::Tensor => self.parse_keyword_identifier("tensor"),
            TokenKind::Union => self.parse_keyword_identifier("union"),
            // Allow control flow keywords as identifiers in expression contexts
            // Simple uses these as variable names (e.g., `var continue = true; while continue:`)
            TokenKind::Continue => self.parse_keyword_identifier("continue"),
            TokenKind::Break => self.parse_keyword_identifier("break"),
            TokenKind::Return => self.parse_keyword_identifier("return"),
            // Allow 'var' as identifier in expression contexts (e.g., match arm with var binding)
            TokenKind::Var => self.parse_keyword_identifier("var"),
            // Allow 'mock' as identifier in expression contexts
            TokenKind::Mock => self.parse_keyword_identifier("mock"),
            // Additional keywords usable as identifiers in expression contexts
            // (parameter names, variable names, function calls)
            TokenKind::By => self.parse_keyword_identifier("by"),
            TokenKind::Onto => self.parse_keyword_identifier("onto"),
            TokenKind::Mod => self.parse_keyword_identifier("mod"),
            TokenKind::Where => self.parse_keyword_identifier("where"),
            TokenKind::Import => self.parse_keyword_identifier("import"),
            TokenKind::Auto => self.parse_keyword_identifier("auto"),
            TokenKind::Requires => self.parse_keyword_identifier("requires"),
            TokenKind::Export => self.parse_keyword_identifier("export"),
            TokenKind::Use => self.parse_keyword_identifier("use"),
            TokenKind::With => self.parse_keyword_identifier("with"),
            TokenKind::On => self.parse_keyword_identifier("on"),
            TokenKind::Into => self.parse_keyword_identifier("into"),
            TokenKind::Bind => self.parse_keyword_identifier("bind"),
            TokenKind::Unwrap => self.parse_keyword_identifier("unwrap"),
            // 'me' is the mutable-self keyword; treat it like 'self' in expression context
            // so that `me.field` and `me.method()` work.
            TokenKind::Me => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
            _ => Err(ParseError::unexpected_token(
                "identifier",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_keyword_identifier(&mut self, keyword: &str) -> Result<Expr, ParseError> {
        self.advance();
        Ok(Expr::Identifier(keyword.to_string()))
    }

    fn parse_identifier_or_struct(&mut self, name: &str) -> Result<Expr, ParseError> {
        let name = name.to_string();
        self.advance();
        // Check for path expression: Name::Variant
        // DEPRECATED: Use dot syntax instead (Name.Variant)
        if self.check(&TokenKind::DoubleColon) {
            // Emit deprecation warning for :: syntax
            let colon_span = self.current.span;
            let warning = ErrorHint {
                level: ErrorHintLevel::Warning,
                message: "Deprecated syntax for static method/variant access".to_string(),
                span: colon_span,
                suggestion: Some("Use dot syntax (.) instead of double colon (::)".to_string()),
                help: Some("Example: Type.new() instead of Type::new()".to_string()),
            };
            self.error_hints.push(warning);

            let mut segments = vec![name];
            while self.check(&TokenKind::DoubleColon) {
                self.advance(); // consume '::'

                // Handle turbofish syntax: name::<T>() — skip generic args
                // Emit deprecation warning but parse successfully
                if self.check(&TokenKind::Lt) {
                    let turbo_span = self.current.span;
                    let warning = ErrorHint {
                        level: ErrorHintLevel::Warning,
                        message: "Deprecated: turbofish ::<T> syntax".to_string(),
                        span: turbo_span,
                        suggestion: Some("Generic type arguments are inferred automatically".to_string()),
                        help: Some("Remove ::<T> — the compiler infers type parameters".to_string()),
                    };
                    self.error_hints.push(warning);

                    // Skip generic args: consume < ... > with nesting support
                    self.advance(); // consume '<'
                    let mut depth = 1u32;
                    while depth > 0 && !self.is_at_end() {
                        if self.check(&TokenKind::Lt) {
                            depth += 1;
                        } else if self.check(&TokenKind::Gt) {
                            depth -= 1;
                            if depth == 0 {
                                self.advance(); // consume final '>'
                                break;
                            }
                        } else if self.check(&TokenKind::ShiftRight) {
                            // >> counts as two > closings
                            if depth <= 2 {
                                depth = 0;
                                self.advance(); // consume '>>'
                                break;
                            }
                            depth -= 2;
                        }
                        self.advance();
                    }
                    break; // Done with path after turbofish
                }

                // Use expect_method_name to allow keywords like 'new', 'type', etc.
                let segment = self.expect_method_name()?;
                segments.push(segment);
            }
            // If only one segment, return as Identifier instead of Path
            if segments.len() == 1 {
                Ok(Expr::Identifier(segments.into_iter().next().unwrap()))
            } else {
                Ok(Expr::Path(segments))
            }
        // Check for struct initialization: Name { field: value, ... }
        // Allow both uppercase (Point { x: 1 }) and lowercase (text { data: ptr }) names
        // Disambiguate from dict literals by checking if `{ identifier :` pattern follows
        } else if self.check(&TokenKind::LBrace)
            && !self.no_brace_postfix
            && (name.chars().next().map_or(false, |c| c.is_uppercase()) || self.peek_is_struct_init())
        {
            self.advance(); // consume '{'
                            // Skip newlines after opening brace
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            let mut fields = Vec::new();
            while !self.check(&TokenKind::RBrace) {
                let field_name = self.expect_identifier()?;
                // Skip newlines before colon or comma
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }

                // Check for shorthand syntax: { x, y } instead of { x: x, y: y }
                let value = if self.check(&TokenKind::Colon) {
                    // Explicit value: field: value
                    self.advance(); // consume ':'
                                    // Skip newlines after colon
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    self.parse_expression()?
                } else {
                    // Shorthand: field means field: field
                    Expr::Identifier(field_name.clone())
                };

                // Skip newlines after value
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                fields.push((field_name, value));
                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
                    // Skip newlines after comma
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
            }
            self.expect(&TokenKind::RBrace)?;
            Ok(Expr::StructInit { name, fields })
        } else {
            Ok(Expr::Identifier(name))
        }
    }

    fn parse_vec_keyword(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        // If followed by !, it's a macro invocation
        if self.check(&TokenKind::Bang) {
            self.advance(); // consume !
            let args = self.parse_macro_args()?;
            Ok(Expr::MacroInvocation {
                name: "vec".to_string(),
                args,
            })
        } else if self.check(&TokenKind::LBracket) {
            // SIMD vector literal: vec[1.0, 2.0, 3.0, 4.0]
            self.advance(); // consume '['

            // Skip whitespace
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
                self.advance();
            }

            // Empty vector
            if self.check(&TokenKind::RBracket) {
                self.advance();
                return Ok(Expr::VecLiteral(Vec::new()));
            }

            // Parse elements
            let mut elements = Vec::new();
            elements.push(self.parse_expression()?);

            while self.check(&TokenKind::Comma) {
                self.advance();
                // Skip whitespace after comma
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }
                if self.check(&TokenKind::RBracket) {
                    break;
                }
                elements.push(self.parse_expression()?);
            }
            self.expect(&TokenKind::RBracket)?;
            Ok(Expr::VecLiteral(elements))
        } else {
            // Otherwise return as an identifier (for backward compatibility)
            Ok(Expr::Identifier("vec".to_string()))
        }
    }
}
