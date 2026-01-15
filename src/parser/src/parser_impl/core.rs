//! Core parser implementation
//!
//! This module contains the Parser struct, constructor methods, and main parse entry point.

use std::collections::VecDeque;

use crate::ast::*;
use crate::error::ParseError;
use crate::error_recovery::ErrorHint;
use crate::lexer::Lexer;
use crate::macro_registry::MacroRegistry;
use crate::token::{Span, Token, TokenKind};

/// Maximum iterations allowed in a single parsing loop before detecting a potential infinite loop.
/// This prevents hangs when the lexer doesn't emit proper tokens or token consumption fails.
pub const MAX_LOOP_ITERATIONS: usize = 100_000;

/// Parser mode controlling strictness of no-parentheses call syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ParserMode {
    /// Normal mode: Allow nested no-paren calls (current behavior)
    #[default]
    Normal,
    /// Strict mode: Allow only ONE level of no-paren call.
    /// Inner function calls within arguments must use parentheses.
    /// Used for GPU kernel code to prevent ambiguity.
    Strict,
}

/// Debug mode for parser diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DebugMode {
    /// No debug output
    #[default]
    Off,
    /// Basic debug output (function entry/exit)
    Basic,
    /// Verbose debug output (every token consumed)
    Verbose,
}

pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) current: Token,
    pub(crate) previous: Token,
    #[allow(dead_code)]
    source: &'a str,
    /// Buffer for lookahead tokens (used for multi-token peek operations)
    pub(crate) pending_tokens: VecDeque<Token>,
    /// Parser mode (Normal or Strict)
    pub(crate) mode: ParserMode,
    /// Depth of no-paren calls (for strict mode enforcement)
    pub(crate) no_paren_depth: u32,
    /// Debug mode for diagnostics
    pub(crate) debug_mode: DebugMode,
    /// Call depth for debug tracing
    pub(crate) debug_depth: usize,
    /// Macro registry for LL(1) macro integration
    pub(crate) macro_registry: MacroRegistry,
    /// Current scope for macro symbol registration (e.g., "module", "class:ClassName")
    pub(crate) current_scope: String,
    /// Collected error hints (helpful messages for common mistakes)
    pub(crate) error_hints: Vec<ErrorHint>,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let previous = Token::new(TokenKind::Eof, Span::new(0, 0, 1, 1), String::new());

        let mut parser = Self {
            lexer,
            current,
            previous,
            source,
            pending_tokens: VecDeque::new(),
            mode: ParserMode::Normal,
            no_paren_depth: 0,
            debug_mode: DebugMode::Off,
            debug_depth: 0,
            macro_registry: MacroRegistry::new(),
            current_scope: "module".to_string(),
            error_hints: Vec::new(),
        };

        // Check for common mistakes in the initial token
        // (since it was loaded via lexer.next_token() bypassing advance())
        let next = parser.lexer.next_token();
        parser.pending_tokens.push_back(next.clone());
        let next_token = Some(&parser.pending_tokens[0]);

        use crate::error_recovery::detect_common_mistake;
        if let Some(mistake) = detect_common_mistake(&parser.current, &parser.previous, next_token)
        {
            use crate::error_recovery::{CommonMistake, ErrorHint, ErrorHintLevel};
            let level = match mistake {
                CommonMistake::PythonDef
                | CommonMistake::PythonNone
                | CommonMistake::PythonTrue
                | CommonMistake::PythonFalse
                | CommonMistake::RustLetMut
                | CommonMistake::JavaPublicClass
                | CommonMistake::JavaVoid
                | CommonMistake::JavaNew
                | CommonMistake::JavaThis
                | CommonMistake::TsFunction
                | CommonMistake::TsConst
                | CommonMistake::TsInterface
                | CommonMistake::CppNamespace
                | CommonMistake::CppTemplate
                | CommonMistake::CTypeFirst
                | CommonMistake::MissingColon => ErrorHintLevel::Error,
                CommonMistake::VerboseReturnType
                | CommonMistake::ExplicitSelf
                | CommonMistake::WrongBrackets
                | CommonMistake::CSemicolon
                | CommonMistake::SemicolonAfterBlock => ErrorHintLevel::Warning,
                CommonMistake::TsLet | CommonMistake::PythonSelf | CommonMistake::RustFnMut => {
                    ErrorHintLevel::Info
                }
                CommonMistake::RustLifetime
                | CommonMistake::RustMacro
                | CommonMistake::RustTurbofish
                | CommonMistake::TsArrowFunction
                | CommonMistake::PythonElif => ErrorHintLevel::Hint,
            };

            let hint = ErrorHint {
                level,
                message: format!("Common mistake detected: {}", mistake.suggestion()),
                span: parser.current.span.clone(),
                suggestion: Some(mistake.suggestion()),
                help: Some(mistake.message()),
            };

            parser.error_hints.push(hint);
        }

        parser
    }

    /// Create a parser with LL(1) macro integration enabled.
    /// When enabled, macro contracts are processed at parse time and
    /// introduced symbols are immediately registered in the symbol table.
    pub fn with_ll1_macros(source: &'a str) -> Self {
        let mut parser = Self::new(source);
        parser.macro_registry.set_ll1_mode(true);
        parser
    }

    /// Get a reference to the macro registry
    pub fn macro_registry(&self) -> &MacroRegistry {
        &self.macro_registry
    }

    /// Get a mutable reference to the macro registry
    pub fn macro_registry_mut(&mut self) -> &mut MacroRegistry {
        &mut self.macro_registry
    }

    /// Create a parser with a specific mode (Normal or Strict).
    /// Strict mode requires parentheses for inner function calls within no-paren call arguments.
    pub fn with_mode(source: &'a str, mode: ParserMode) -> Self {
        let mut parser = Self::new(source);
        parser.mode = mode;
        parser
    }

    /// Create a parser with debug mode enabled.
    /// Debug mode outputs parsing trace information to stderr.
    pub fn with_debug(source: &'a str, debug_mode: DebugMode) -> Self {
        let mut parser = Self::new(source);
        parser.debug_mode = debug_mode;
        parser
    }

    /// Set debug mode on an existing parser
    pub fn set_debug_mode(&mut self, mode: DebugMode) {
        self.debug_mode = mode;
    }

    /// Get accumulated error hints (helpful messages for common mistakes)
    pub fn error_hints(&self) -> &[ErrorHint] {
        &self.error_hints
    }

    /// Clear accumulated error hints
    pub fn clear_error_hints(&mut self) {
        self.error_hints.clear();
    }

    /// Output debug trace message if debug mode is enabled
    #[inline]
    pub(crate) fn debug_trace(&self, msg: &str) {
        if self.debug_mode != DebugMode::Off {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}{}", indent, msg);
        }
    }

    /// Output verbose debug trace (token-level)
    #[inline]
    pub(crate) fn debug_verbose(&self, msg: &str) {
        if self.debug_mode == DebugMode::Verbose {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}{}", indent, msg);
        }
    }

    /// Enter a parsing function (for debug tracing)
    #[inline]
    pub(crate) fn debug_enter(&mut self, name: &str) {
        if self.debug_mode != DebugMode::Off {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!(
                "[PARSER] {}> {} (token: {:?})",
                indent, name, self.current.kind
            );
            self.debug_depth += 1;
        }
    }

    /// Exit a parsing function (for debug tracing)
    #[inline]
    pub(crate) fn debug_exit(&mut self, name: &str) {
        if self.debug_mode != DebugMode::Off {
            if self.debug_depth > 0 {
                self.debug_depth -= 1;
            }
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}< {}", indent, name);
        }
    }

    /// Check for potential infinite loop in parsing
    /// Returns an error if iteration count exceeds MAX_LOOP_ITERATIONS
    #[inline]
    pub(crate) fn check_loop_limit(
        &self,
        iterations: usize,
        context: &str,
    ) -> Result<(), ParseError> {
        if iterations >= MAX_LOOP_ITERATIONS {
            Err(ParseError::syntax_error_with_span(
                format!(
                    "Parser iteration limit exceeded in {} (possible infinite loop). \
                     Current token: {:?} at line {}, col {}",
                    context, self.current.kind, self.current.span.line, self.current.span.column
                ),
                self.current.span,
            ))
        } else {
            Ok(())
        }
    }

    pub fn parse(&mut self) -> Result<Module, ParseError> {
        self.debug_trace("Starting parse()");
        let mut items = Vec::new();
        let mut iterations = 0usize;

        while !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_module")?;
            iterations += 1;

            // Skip newlines at top level
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }

            self.debug_verbose(&format!("Parsing item {}", iterations));
            items.push(self.parse_item()?);
        }

        self.debug_trace(&format!("Finished parse(), {} items", items.len()));
        Ok(Module { name: None, items })
    }

    pub(crate) fn parse_item(&mut self) -> Result<Node, ParseError> {
        // Skip leading newlines
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Check for doc comment before item
        let doc_comment = self.try_parse_doc_comment();

        match &self.current.kind {
            TokenKind::Hash => self.parse_attributed_item_with_doc(doc_comment),
            TokenKind::At => self.parse_decorated_function_with_doc(doc_comment),
            TokenKind::Fn => self.parse_function_with_doc(doc_comment),
            TokenKind::Async => self.parse_async_function_with_doc(doc_comment),
            TokenKind::Sync => self.parse_sync_function_with_doc(doc_comment),
            TokenKind::Struct => self.parse_struct_with_doc(doc_comment),
            TokenKind::Class => self.parse_class_with_doc(doc_comment),
            TokenKind::Enum => self.parse_enum_with_doc(doc_comment),
            TokenKind::Union => self.parse_union_with_doc(doc_comment),
            TokenKind::Trait => self.parse_trait_with_doc(doc_comment),
            TokenKind::Mixin => self.parse_mixin(),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Actor => self.parse_actor(),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_doc(doc_comment)
            }
            TokenKind::Mut => self.parse_mut_let(), // Legacy: mut let
            TokenKind::Let => self.parse_let(),     // Legacy: let
            TokenKind::Val => self.parse_val(),     // New: val (immutable)
            TokenKind::Var => self.parse_var(),     // New: var (mutable)
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => self.parse_static(),
            TokenKind::Shared => self.parse_shared_let(),
            TokenKind::Ghost => self.parse_ghost_let(),
            TokenKind::Type => {
                // Check if this is a type alias (type Name = ...) or expression (expect type to eq)
                // Simple heuristic: type alias names are PascalCase (start with uppercase)
                // Expression context uses lowercase like "expect type to eq"
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });

                // Check if next token is an uppercase identifier (type alias pattern)
                if let TokenKind::Identifier { name: name, .. } = &next.kind {
                    if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                        // PascalCase identifier after 'type' - treat as type alias
                        self.parse_type_alias()
                    } else {
                        // lowercase identifier after 'type' - treat as expression
                        self.parse_expression_or_assignment()
                    }
                } else {
                    // Not followed by identifier - treat 'type' as expression
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Unit => self.parse_unit(),
            TokenKind::HandlePool => self.parse_handle_pool(),
            TokenKind::Extern => self.parse_extern(),
            TokenKind::Macro => self.parse_macro_def(),
            // Module system (Features #104-111)
            TokenKind::Use => self.parse_use(),
            TokenKind::Import => self.parse_import(), // alias for use
            TokenKind::Mod => self.parse_mod(Visibility::Private, vec![]),
            TokenKind::Common => self.parse_common_use(),
            TokenKind::Export => self.parse_export_use(),
            TokenKind::Auto => self.parse_auto_import(),
            TokenKind::Requires => self.parse_requires_capabilities(),
            // AOP & Unified Predicates (#1000-1050)
            TokenKind::On => self.parse_aop_advice().map(Node::AopAdvice),
            TokenKind::Bind => {
                // Disambiguate between:
                // - DI binding: `bind on pc{...} -> Impl`
                // - Interface binding: `bind [static|dyn] Interface = ImplType`
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });
                if matches!(next.kind, TokenKind::On) {
                    self.parse_di_binding().map(Node::DiBinding)
                } else {
                    self.parse_interface_binding()
                }
            }
            TokenKind::Forbid | TokenKind::Allow => {
                self.parse_arch_rule().map(Node::ArchitectureRule)
            }
            TokenKind::Mock => self.parse_mock_decl().map(Node::MockDecl),
            TokenKind::If => self.parse_if(),
            TokenKind::IfSuspend => self.parse_if_suspend(),
            TokenKind::Match => self.parse_match_stmt(),
            TokenKind::For => self.parse_for(),
            TokenKind::ForSuspend => self.parse_for_suspend(),
            TokenKind::While => self.parse_while(),
            TokenKind::WhileSuspend => self.parse_while_suspend(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => self.parse_break(),
            TokenKind::Continue => self.parse_continue(),
            TokenKind::Context => {
                // Check if this is a context statement (context expr:) or function call (context(...)) or BDD DSL (context "string":)
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });

                // If next token is a string literal, treat as BDD expression (no-paren call)
                if matches!(
                    &next.kind,
                    TokenKind::String(_) | TokenKind::RawString(_) | TokenKind::FString(_)
                ) {
                    self.parse_expression_or_assignment()
                // If next token is an opening paren, treat as function call
                } else if matches!(&next.kind, TokenKind::LParen) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_context()
                }
            }
            TokenKind::With => self.parse_with(),
            // Gherkin-style system test DSL (Features #606-610)
            TokenKind::Feature => self.parse_feature(),
            TokenKind::Scenario => self.parse_scenario(),
            TokenKind::Examples => self.parse_examples(),
            TokenKind::Given | TokenKind::When | TokenKind::Then | TokenKind::AndThen => {
                self.parse_step_ref_as_node()
            }
            _ => self.parse_expression_or_assignment(),
        }
    }

    pub(crate) fn parse_block(&mut self) -> Result<Block, ParseError> {
        // Expect NEWLINE then INDENT
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        self.parse_block_body()
    }

    /// Parse block body (assumes INDENT has already been consumed).
    /// Used when we need to manually handle what comes before the block body.
    pub(crate) fn parse_block_body(&mut self) -> Result<Block, ParseError> {
        self.debug_enter("parse_block_body");
        let start_span = self.current.span;

        let mut statements = Vec::new();
        let mut iterations = 0usize;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_block_body")?;
            iterations += 1;

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            statements.push(self.parse_item()?);

            // Consume newline after statement if present
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        self.debug_exit("parse_block_body");
        Ok(Block {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            statements,
        })
    }

    pub(crate) fn parse_parameters(&mut self) -> Result<Vec<Parameter>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();

        // Skip newlines after opening paren (allow multi-line parameter lists)
        self.skip_newlines();

        while !self.check(&TokenKind::RParen) {
            let param_span = self.current.span;

            // Check for @inject attribute on parameter (#1013)
            let inject = if self.check(&TokenKind::At) {
                self.advance();
                let attr_name = self.expect_identifier()?;
                if attr_name != "inject" {
                    return Err(ParseError::UnexpectedToken {
                        expected: "inject".to_string(),
                        found: attr_name,
                        span: self.current.span,
                    });
                }
                true
            } else {
                false
            };

            let mutability = if self.check(&TokenKind::Mut) {
                self.advance();
                Mutability::Mutable
            } else {
                Mutability::Immutable
            };

            // Allow 'self' as a parameter name for method definitions
            let name = if self.check(&TokenKind::Self_) {
                self.advance();
                "self".to_string()
            } else {
                self.expect_identifier()?
            };

            let ty = if self.check(&TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };

            // Check for variadic parameter (e.g., items: T...)
            let variadic = if self.check(&TokenKind::Ellipsis) {
                self.advance();
                true
            } else {
                false
            };

            let default = if self.check(&TokenKind::Assign) {
                self.advance();
                Some(self.parse_expression()?)
            } else {
                None
            };

            params.push(Parameter {
                span: param_span,
                name,
                ty,
                default,
                mutability,
                inject,
                variadic,
            });

            // Handle comma or newline between parameters
            if !self.check(&TokenKind::RParen) {
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Skip newlines after comma (allow multi-line parameter lists)
                    self.skip_newlines();
                } else if self.check(&TokenKind::Newline) {
                    // Allow newline without comma in multi-line parameter lists
                    self.skip_newlines();
                } else {
                    return Err(ParseError::unexpected_token(
                        "comma or newline",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    /// Parse parenthesized type list: `(Type1, Type2, ...)`
    pub(crate) fn parse_paren_type_list(&mut self) -> Result<Vec<Type>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut types = Vec::new();
        while !self.check(&TokenKind::RParen) {
            types.push(self.parse_type()?);
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(types)
    }
}
