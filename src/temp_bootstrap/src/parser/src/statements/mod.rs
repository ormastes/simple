//! Statement parsing module
//!
//! This module contains all statement parsing logic including:
//! - Variable declarations (let, mut let, const, static)
//! - Control flow (if, for, while, loop, match)
//! - Jump statements (return, break, continue)
//! - Context and with statements
//! - Contract blocks (requires/ensures/invariant) - LLM-friendly feature #400

mod contract;

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::Parser;

impl<'a> Parser<'a> {
    /// Helper to parse a number (float or int) as f64.
    fn parse_number_as_f64(&mut self) -> Result<f64, ParseError> {
        if let TokenKind::Float(f) = &self.current.kind {
            let val = *f;
            self.advance();
            Ok(val)
        } else if let TokenKind::Integer(i) = &self.current.kind {
            let val = *i as f64;
            self.advance();
            Ok(val)
        } else {
            Err(ParseError::unexpected_token(
                "number",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Helper to parse a unit variant (suffix = factor)
    fn parse_unit_variant(&mut self) -> Result<UnitVariant, ParseError> {
        let suffix = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let factor = self.parse_number_as_f64()?;
        Ok(UnitVariant { suffix, factor })
    }
    // === Variable Declarations ===

    /// Parse `var name = expr` (mutable variable in Simple syntax)
    pub(crate) fn parse_var(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Var)?;
        self.parse_let_impl(start_span, Mutability::Mutable)
    }

    /// Parse `me method_name(...)` (mutable method in Simple syntax)
    /// Translates to a regular function with implicit mutable self
    pub(crate) fn parse_me_method(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Me)?;

        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let mut params = self.parse_parameters()?;

        // Add implicit mutable self as first parameter
        params.insert(
            0,
            Parameter {
                span: start_span,
                name: "self".to_string(),
                ty: None,
                default: None,
                mutability: Mutability::Mutable,
            },
        );

        // Handle multi-line method signatures where -> is on a continuation line:
        //   me method(params)
        //       -> ReturnType:
        //       body...
        let mut consumed_continuation_indent = false;
        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else if self.check(&TokenKind::Newline) {
            // Peek ahead: check if Newline -> Indent -> Arrow
            // Ensure tok1 is in pending_token (non-destructive peek)
            let tok1 = if let Some(ref pt) = self.pending_token {
                pt.clone()
            } else {
                let t = self.lexer.next_token();
                self.pending_token = Some(t.clone());
                t
            };
            let is_continuation = if tok1.kind == TokenKind::Indent {
                let tok2 = self.lexer.next_token();
                let result = tok2.kind == TokenKind::Arrow;
                if result {
                    // Consume: Newline, Indent, Arrow
                    self.advance(); // consume Newline, current = Indent (from pending)
                    self.pending_token = Some(tok2); // set Arrow as pending
                    self.advance(); // consume Indent, current = Arrow
                    self.advance(); // consume Arrow, current = next token
                    consumed_continuation_indent = true;
                    true
                } else {
                    // tok1 is already in pending_token, push tok2 back
                    self.lexer.pending_tokens.push(tok2);
                    false
                }
            } else {
                // tok1 is already in pending_token, not a continuation
                false
            };
            if is_continuation {
                Some(self.parse_type()?)
            } else {
                None
            }
        } else {
            None
        };

        let where_clause = self.parse_where_clause()?;

        self.skip_newlines();

        let contract = if self.check(&TokenKind::In)
            || self.check(&TokenKind::Invariant)
            || self.check(&TokenKind::Out)
            || self.check(&TokenKind::OutErr)
            || self.check(&TokenKind::Requires)
            || self.check(&TokenKind::Ensures)
        {
            self.parse_contract_block()?
        } else {
            None
        };

        self.skip_newlines();

        // Check for bodiless declaration (extern class methods, trait methods, etc.)
        let is_bodiless = !self.check(&TokenKind::Colon) && (
            self.check(&TokenKind::Newline) || self.check(&TokenKind::Eof) || self.check(&TokenKind::Dedent)
            || self.check(&TokenKind::Fn) || self.check(&TokenKind::Me) || self.check(&TokenKind::Static)
            || self.check(&TokenKind::Pub) || self.check(&TokenKind::Hash) || self.check(&TokenKind::At)
            || self.check(&TokenKind::Extern) || self.check(&TokenKind::Async)
        );
        if is_bodiless {
            return Ok(Node::Function(FunctionDef {
                span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                name,
                generic_params,
                params,
                return_type,
                body: Block {
                    span: Span::new(start_span.start, start_span.start, start_span.line, start_span.column),
                    statements: vec![],
                },
                where_clause,
                decorators: vec![],
                effect: None,
                visibility: Visibility::Private,
                attributes: vec![],
                doc_comment: None,
                contract,
                is_abstract: true,
            }));
        }

        self.expect(&TokenKind::Colon)?;
        let body = if consumed_continuation_indent {
            // Multi-line signature: parse body directly until Dedent
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            let block_span = self.current.span;
            let mut stmts = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                self.skip_newlines();
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                stmts.push(self.parse_item()?);
            }
            self.consume_dedent();
            Block {
                span: Span::new(block_span.start, self.previous.span.end, block_span.line, block_span.column),
                statements: stmts,
            }
        } else {
            self.parse_block()?
        };

        Ok(Node::Function(FunctionDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            params,
            return_type,
            where_clause,
            body,
            visibility: Visibility::Private,
            effect: None,
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract,
            is_abstract: false,
        }))
    }

    /// Parse `bitfield Name:` (bit-level data structure)
    /// Treated as a struct for now
    pub(crate) fn parse_bitfield(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Bitfield)?;

        let name = self.expect_identifier()?;

        // Optional underlying type: bitfield Flags(u8):
        if self.check(&TokenKind::LParen) {
            self.advance();
            let _underlying = self.parse_type()?;
            self.expect(&TokenKind::RParen)?;
        }

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        // Parse bitfield as a struct with the body as fields
        Ok(Node::Struct(StructDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params: vec![],
            where_clause: vec![],
            fields: vec![],
            methods: body.statements.into_iter().filter_map(|s| {
                if let Node::Function(f) = s {
                    Some(f)
                } else {
                    None
                }
            }).collect(),
            visibility: Visibility::Private,
            attributes: vec![],
            doc_comment: None,
            invariant: None,
        }))
    }

    /// Parse `alias NewName = ExistingName` (class/type alias)
    pub(crate) fn parse_alias(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Alias)?;

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        Ok(Node::TypeAlias(TypeAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            visibility: Visibility::Private,
            where_clause: None,
        }))
    }

    pub(crate) fn parse_mut_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mut)?;
        self.expect(&TokenKind::Let)?;
        self.parse_let_impl(start_span, Mutability::Mutable)
    }

    pub(crate) fn parse_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Let)?;
        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };
        self.parse_let_impl(start_span, mutability)
    }

    fn parse_let_impl(
        &mut self,
        start_span: Span,
        mutability: Mutability,
    ) -> Result<Node, ParseError> {
        let pattern = self.parse_pattern()?;
        let ty = self.parse_optional_type_annotation()?;
        let value = self.parse_optional_assignment()?;

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            ty,
            value,
            mutability,
        }))
    }

    /// Parse optional type annotation `: Type`
    fn parse_optional_type_annotation(&mut self) -> Result<Option<Type>, ParseError> {
        if self.check(&TokenKind::Colon) {
            self.advance();
            Ok(Some(self.parse_type()?))
        } else {
            Ok(None)
        }
    }

    /// Parse optional assignment `= expr`
    fn parse_optional_assignment(&mut self) -> Result<Option<Expr>, ParseError> {
        if self.check(&TokenKind::Assign) {
            self.advance();
            // Skip newline+indent after `=` for multi-line expressions:
            //   val x =
            //       "some value"
            let continuation_depth = self.skip_whitespace_for_continuation();
            let expr = self.parse_expression()?;
            self.consume_continuation_dedents(continuation_depth);
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// Helper to parse name, type annotation, and assigned value for const/static
    fn parse_named_value(&mut self) -> Result<(String, Option<Type>, Expr), ParseError> {
        let name = self.expect_identifier()?;
        let ty = self.parse_optional_type_annotation()?;
        self.expect(&TokenKind::Assign)?;
        // Skip newline+indent after `=` for multi-line expressions
        let continuation_depth = self.skip_whitespace_for_continuation();
        let value = self.parse_expression()?;
        self.consume_continuation_dedents(continuation_depth);
        Ok((name, ty, value))
    }

    /// Parse optional let-pattern syntax: `let PATTERN =`
    /// Used by if-let and while-let constructs
    fn parse_optional_let_pattern(&mut self) -> Result<(Option<Pattern>, Expr), ParseError> {
        if self.check(&TokenKind::Let) || self.check(&TokenKind::Var) {
            // Peek ahead: if the token after `val`/`var` is an operator that cannot start a pattern,
            // treat it as a variable name in expression context (e.g., `if val < min_val:`)
            let next = self.pending_token.clone()
                .unwrap_or_else(|| self.lexer.next_token());
            self.pending_token = Some(next.clone());
            let is_expression_context = matches!(
                next.kind,
                TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq
                | TokenKind::Eq | TokenKind::NotEq
                | TokenKind::Plus | TokenKind::Star | TokenKind::Slash
                | TokenKind::Percent | TokenKind::DoubleStar | TokenKind::DoubleSlash
                | TokenKind::Dot | TokenKind::Pipe | TokenKind::Ampersand
                | TokenKind::And | TokenKind::Or
                | TokenKind::Is | TokenKind::In
                | TokenKind::ShiftLeft | TokenKind::ShiftRight
                | TokenKind::Assign  // `val = expr` is assignment, not let-pattern
                | TokenKind::PlusAssign | TokenKind::MinusAssign
                | TokenKind::StarAssign | TokenKind::SlashAssign
                | TokenKind::Colon  // `val: type` is type annotation
                | TokenKind::Newline | TokenKind::Eof  // just `val` alone
                | TokenKind::RParen  // `(val)` - val in parens
                | TokenKind::Comma  // `f(val, x)` - val in argument list
                | TokenKind::Question  // `val?` optional chain
                | TokenKind::DoubleQuestion  // `val ?? default`
            );
            if is_expression_context {
                // Treat `val`/`var` as expression (variable named 'val'/'var')
                return Ok((None, self.parse_expression()?));
            }
            self.advance();
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::Assign)?;
            let expr = self.parse_expression()?;
            Ok((Some(pattern), expr))
        } else {
            Ok((None, self.parse_expression()?))
        }
    }

    /// Parse use path and target (shared by use, common use, export use)
    /// Supports both Python-style (module.{A, B}) and Rust-style (module::{A, B})
    fn parse_use_path_and_target(&mut self) -> Result<(ModulePath, ImportTarget), ParseError> {
        let path = self.parse_module_path()?;

        // Check for Rust-style :: before { or *
        if self.check(&TokenKind::DoubleColon) {
            self.advance(); // consume ::
        }

        // Handle colon-separated imports: import module: Name1, Name2
        if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            // Skip whitespace after colon
            self.skip_whitespace_tokens();
            let mut targets = Vec::new();
            loop {
                let mut name = self.expect_identifier()?;
                // Handle `?` suffix (e.g., `iter_empty?`)
                if self.check(&TokenKind::Question) {
                    self.advance();
                    name = format!("{}?", name);
                }
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_identifier()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    self.skip_whitespace_tokens();
                } else {
                    break;
                }
            }
            let target = if targets.len() == 1 {
                targets.remove(0)
            } else {
                ImportTarget::Group(targets)
            };
            return Ok((path, target));
        }

        if self.check(&TokenKind::Star) || self.check(&TokenKind::LBrace) {
            let target = self.parse_import_target(None)?;
            Ok((path, target))
        } else if self.check(&TokenKind::LParen) {
            // Handle parenthesized import list: use .module (Name1, Name2)
            self.advance(); // consume '('
            // Skip whitespace after opening paren (for multi-line import lists)
            self.skip_whitespace_tokens();
            let mut targets = Vec::new();
            while !self.check(&TokenKind::RParen) {
                let mut name = self.expect_identifier()?;
                // Handle `?` suffix (e.g., `iter_empty?`)
                if self.check(&TokenKind::Question) {
                    self.advance();
                    name = format!("{}?", name);
                }
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_identifier()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);
                // Skip whitespace after target
                self.skip_whitespace_tokens();
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                    // Skip whitespace after comma
                    self.skip_whitespace_tokens();
                }
            }
            self.expect(&TokenKind::RParen)?;
            Ok((path, ImportTarget::Group(targets)))
        } else {
            let mut segments = path.segments;
            let last = segments.pop().unwrap_or_default();
            let target = self.parse_import_target(Some(last))?;
            Ok((ModulePath::new(segments), target))
        }
    }

    pub(crate) fn parse_const(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Const)?;
        let (name, ty, value) = self.parse_named_value()?;

        Ok(Node::Const(ConstStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            value,
            visibility: Visibility::Private,
        }))
    }

    pub(crate) fn parse_static(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Static)?;

        // If followed by 'fn', parse as static function/method
        if self.check(&TokenKind::Fn) {
            return self.parse_function();
        }
        // If followed by 'async fn', parse as static async function
        if self.check(&TokenKind::Async) {
            self.advance();
            let mut func = self.parse_function()?;
            if let Node::Function(ref mut f) = func {
                f.effect = Some(Effect::Async);
            }
            return Ok(func);
        }

        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };
        let (name, ty, value) = self.parse_named_value()?;

        Ok(Node::Static(StaticStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            value,
            mutability,
            visibility: Visibility::Private,
        }))
    }

    /// Parse type alias with optional refinement predicate (CTR-020)
    ///
    /// Simple: `type UserId = i64`
    /// Refined: `type PosI64 = i64 where self > 0`
    pub(crate) fn parse_type_alias(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;

        let name = self.expect_identifier()?;

        // Skip optional generic params: type Array2[T] = ...
        let _generic_params = self.parse_generic_params()?;

        // Skip optional type bound: type Iter: Iterator[Item=T]
        if self.check(&TokenKind::Colon) {
            self.advance();
            let _bound = self.parse_type()?;
        }

        // Handle associated type declarations without '=' (e.g., `type Item` in traits)
        if !self.check(&TokenKind::Assign) {
            // Associated type with no value — return with a placeholder type
            return Ok(Node::TypeAlias(TypeAliasDef {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                name,
                ty: Type::Simple("_".to_string()),
                visibility: Visibility::Private,
                where_clause: None,
            }));
        }

        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        // Parse optional refinement predicate: `where self > 0`
        let where_clause = if self.check(&TokenKind::Where) {
            self.advance(); // consume 'where'
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::TypeAlias(TypeAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            visibility: Visibility::Private,
            where_clause,
        }))
    }

    /// Parse unit definition: either standalone or family
    /// Standalone: `unit UserId: i64 as uid`
    /// Family: `unit length(base: f64): m = 1.0, km = 1000.0`
    pub(crate) fn parse_unit(&mut self) -> Result<Node, ParseError> {
        use crate::ast::UnitFamilyDef;

        let start_span = self.current.span;
        self.expect(&TokenKind::Unit)?;

        let mut name = self.expect_identifier()?;

        // Handle `unit family Name: Type as suffix` - `family` keyword
        let is_family = name == "family";
        if is_family {
            name = self.expect_identifier()?;
        }

        // Check if this is a unit family: unit name(base: Type): ...
        if self.check(&TokenKind::LParen) {
            // Unit family syntax
            self.advance(); // consume '('

            // Parse (base: Type) - we expect "base" as the identifier
            let _base_name = self.expect_identifier()?; // "base"
            self.expect(&TokenKind::Colon)?;
            let base_type = self.parse_type()?;
            self.expect(&TokenKind::RParen)?;

            self.expect(&TokenKind::Colon)?;

            // Parse variants: suffix = factor, suffix = factor, ...
            // Can be on same line or indented block
            let mut variants = Vec::new();

            // Skip newline if present
            if self.check(&TokenKind::Newline) {
                self.advance();
                // Check for indented block
                if self.check(&TokenKind::Indent) {
                    self.advance();
                    // Parse indented variants
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        // Skip newlines between variants
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) {
                            break;
                        }
                        variants.push(self.parse_unit_variant()?);

                        // Skip comma or newline
                        if self.check(&TokenKind::Comma) {
                            self.advance();
                        }
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    // Consume dedent
                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                }
            } else {
                // Single line: m = 1.0, km = 1000.0
                loop {
                    variants.push(self.parse_unit_variant()?);
                    if !self.check(&TokenKind::Comma) {
                        break;
                    }
                    self.advance(); // consume comma
                }
            }

            return Ok(Node::UnitFamily(UnitFamilyDef {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                name,
                base_type,
                variants,
                visibility: Visibility::Private,
            }));
        }

        // Standalone unit syntax:
        // Single-base: unit UserId: i64 as uid
        // Multi-base:  unit IpAddr: str | u32 as ip
        self.expect(&TokenKind::Colon)?;

        // Parse base type (can be a union type for multi-base)
        // parse_type() handles union types: str | u32 -> Type::Union([str, u32])
        let base_type = self.parse_type()?;

        // Convert to base_types Vec:
        // - Single type: [Type]
        // - Union type: [Type1, Type2, ...]
        let base_types = match base_type {
            Type::Union(types) => types,
            other => vec![other],
        };

        self.expect(&TokenKind::As)?;
        let suffix = self.expect_identifier()?;

        // If this was `unit family Name: Type as suffix`, check for indented block of variants
        if is_family {
            let base_type = if base_types.len() == 1 {
                base_types.into_iter().next().unwrap()
            } else {
                Type::Union(base_types)
            };

            let mut variants = Vec::new();
            // Skip newline if present
            if self.check(&TokenKind::Newline) {
                self.advance();
                // Check for indented block
                if self.check(&TokenKind::Indent) {
                    self.advance();
                    // Parse indented variants
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        // Skip newlines between variants
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) {
                            break;
                        }
                        variants.push(self.parse_unit_variant()?);

                        // Skip comma or newline
                        if self.check(&TokenKind::Comma) {
                            self.advance();
                        }
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    // Consume dedent
                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                }
            }

            return Ok(Node::UnitFamily(UnitFamilyDef {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                name,
                base_type,
                variants,
                visibility: Visibility::Private,
            }));
        }

        Ok(Node::Unit(UnitDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            base_types,
            suffix,
            visibility: Visibility::Private,
        }))
    }

    /// Parse `try: ... catch name: ...` blocks.
    /// Since try/catch is not native Simple syntax, we consume the blocks
    /// and emit a nil expression as a placeholder.
    pub(crate) fn parse_try_catch(&mut self) -> Result<Node, ParseError> {
        // Consume 'try' identifier
        self.advance(); // consume 'try'
        self.expect(&TokenKind::Colon)?;
        let _try_body = self.parse_block()?;

        // Skip newlines between try and catch
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Check for `catch name:` or `catch:`
        if let TokenKind::Identifier(name) = &self.current.kind.clone() {
            if name == "catch" {
                self.advance(); // consume 'catch'
                // Optional catch variable name
                if let TokenKind::Identifier(_) = &self.current.kind {
                    self.advance(); // consume catch variable name
                }
                if self.check(&TokenKind::Colon) {
                    self.expect(&TokenKind::Colon)?;
                    let _catch_body = self.parse_block()?;
                }
            }
        }

        // Emit nil as placeholder - try/catch is consumed for parsing validation only
        Ok(Node::Expression(Expr::Nil))
    }

    pub(crate) fn parse_extern(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Extern)?;
        // Handle `extern async fn` by skipping the async keyword
        if self.check(&TokenKind::Async) {
            self.advance();
        }
        // Handle `extern class/struct` by delegating to class/struct parser
        if self.check(&TokenKind::Class) {
            return self.parse_class();
        }
        if self.check(&TokenKind::Struct) {
            return self.parse_struct();
        }
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        // Skip optional generic params: extern fn name<T, U>(...)
        let _generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        Ok(Node::Extern(ExternDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            params,
            return_type,
            visibility: Visibility::Private,
        }))
    }

    // === Control Flow ===

    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;
        // Handle `if~` suspension syntax - just consume the tilde
        if self.check(&TokenKind::Tilde) {
            self.advance();
        }

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        // Accept both ':' and 'then' as delimiters for if condition
        if self.check(&TokenKind::Colon) {
            self.advance();
        } else if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "then") {
            self.advance();
        } else {
            self.expect(&TokenKind::Colon)?;
        }
        let then_block = self.parse_block_or_inline()?;

        // Helper closure to skip newlines before elif/else
        fn skip_newlines_before_elif_else(parser: &mut Parser) {
            while parser.check(&TokenKind::Newline) {
                let next = parser
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| parser.lexer.next_token());
                parser.pending_token = Some(next.clone());
                if next.kind == TokenKind::Elif || next.kind == TokenKind::Else {
                    parser.advance(); // consume newline
                } else {
                    break;
                }
            }
        }

        skip_newlines_before_elif_else(self);

        let mut elif_branches = Vec::new();

        // Parse elif / else if chains in a loop
        loop {
            if self.check(&TokenKind::Elif) {
                self.advance();
                let (_elif_let_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_block_or_inline()?;
                elif_branches.push((elif_condition, elif_block));
                skip_newlines_before_elif_else(self);
            } else if self.check(&TokenKind::Else) {
                // Peek ahead: is this `else if` (treated as elif) or `else:` (final else)?
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::If {
                    // `else if` => treat as elif
                    self.advance(); // consume 'else'
                    self.advance(); // consume 'if'
                    let (_elif_let_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                    self.expect(&TokenKind::Colon)?;
                    let elif_block = self.parse_block_or_inline()?;
                    elif_branches.push((elif_condition, elif_block));
                    skip_newlines_before_elif_else(self);
                } else {
                    break; // `else:` — will be handled below
                }
            } else {
                break;
            }
        }

        let else_block = if self.check(&TokenKind::Else) {
            self.advance();
            // Accept both `else:` and `else expr` (colon-less inline else)
            if self.check(&TokenKind::Colon) {
                self.advance();
            }
            Some(self.parse_block_or_inline()?)
        } else {
            None
        };

        Ok(Node::If(IfStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            then_block,
            elif_branches,
            else_block,
        }))
    }

    pub(crate) fn parse_for(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;
        // Handle `for~` suspension syntax - just consume the tilde
        if self.check(&TokenKind::Tilde) {
            self.advance();
        }

        let first = self.parse_pattern()?;
        // Handle implicit tuple pattern: for i, x in ...
        let pattern = if self.check(&TokenKind::Comma) {
            let mut patterns = vec![first];
            while self.check(&TokenKind::Comma) {
                self.advance();
                patterns.push(self.parse_pattern()?);
            }
            Pattern::Tuple(patterns)
        } else {
            first
        };
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block_or_inline()?;

        Ok(Node::For(ForStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            iterable,
            body,
        }))
    }

    pub(crate) fn parse_while(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;
        // Handle `while~` suspension syntax - just consume the tilde
        if self.check(&TokenKind::Tilde) {
            self.advance();
        }

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block_or_inline()?;

        Ok(Node::While(WhileStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            body,
        }))
    }

    pub(crate) fn parse_loop(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Loop)?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Loop(LoopStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }

    pub(crate) fn parse_context(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        let context = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Context(ContextStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            context,
            body,
        }))
    }

    pub(crate) fn parse_with(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::With)?;

        let resource = self.parse_expression()?;

        // Optional "as name"
        let name = if self.check(&TokenKind::As) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::With(WithStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            resource,
            name,
            body,
        }))
    }

    // === Jump Statements ===

    pub(crate) fn parse_return(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Return)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Return(ReturnStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_break(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Break)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Break(BreakStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_continue(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Continue)?;

        Ok(Node::Continue(ContinueStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
        }))
    }

    // === Match ===

    pub(crate) fn parse_match_stmt(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Match)?;

        let subject = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;

        // Handle inline match: match x: case A: val1; case B: val2
        if !self.check(&TokenKind::Newline) {
            let mut arms = Vec::new();
            loop {
                arms.push(self.parse_match_arm()?);
                // Check for semicolon separator between inline arms
                if self.check(&TokenKind::Semicolon) {
                    self.advance();
                    // Skip whitespace
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    if self.is_at_end() || self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                        break;
                    }
                } else {
                    break;
                }
            }
            return Ok(Node::Match(MatchStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                subject,
                arms,
            }));
        }

        self.expect(&TokenKind::Newline)?;
        if self.check(&TokenKind::Indent) {
            self.expect(&TokenKind::Indent)?;

            let mut arms = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    break;
                }
                // Skip inline val/var bindings inside match blocks
                // e.g., `match result:\n    val _tup = (a, b)\n    case Ok(_tup): ...`
                if self.check(&TokenKind::Let) || self.check(&TokenKind::Var) {
                    self.advance(); // consume val/var
                    let _name = self.expect_identifier();
                    if self.check(&TokenKind::Assign) {
                        self.advance();
                        let _expr = self.parse_expression();
                    }
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    continue;
                }
                arms.push(self.parse_match_arm()?);
            }

            if self.check(&TokenKind::Dedent) {
                self.advance();
            }

            Ok(Node::Match(MatchStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                subject,
                arms,
            }))
        } else if self.check(&TokenKind::Case)
            || matches!(&self.current.kind, TokenKind::Identifier(_))
            || self.check(&TokenKind::Underscore)
        {
            // Inside brackets (no indent tracking), match arms appear
            // after newline without indent
            let mut arms = Vec::new();
            loop {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.is_at_end()
                    || self.check(&TokenKind::RParen)
                    || self.check(&TokenKind::RBrace)
                    || self.check(&TokenKind::Dedent)
                {
                    break;
                }
                // Inside brackets (no indent tracking), match arms start with
                // `case`, a pattern-starting token (identifier, literal, underscore,
                // paren, bracket), or certain keywords like `_`.
                // If we see val/var/fn/for/if/while/return/etc., the match
                // block is done and the enclosing block continues.
                let can_be_arm = matches!(&self.current.kind,
                    TokenKind::Case
                    | TokenKind::Identifier(_)
                    | TokenKind::Underscore
                    | TokenKind::Integer(_)
                    | TokenKind::Float(_)
                    | TokenKind::String(_)
                    | TokenKind::FString(_)
                    | TokenKind::RawString(_)
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::Nil
                    | TokenKind::LParen
                    | TokenKind::LBracket
                    | TokenKind::Not
                    | TokenKind::Minus
                );
                if !can_be_arm {
                    break;
                }
                arms.push(self.parse_match_arm()?);
                if self.check(&TokenKind::Semicolon) {
                    self.advance();
                }
            }
            Ok(Node::Match(MatchStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                subject,
                arms,
            }))
        } else {
            // Empty match body
            Ok(Node::Match(MatchStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                subject,
                arms: vec![],
            }))
        }
    }

    pub(crate) fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;
        if self.check(&TokenKind::Case) {
            self.advance();
        }
        // Set flag so pattern parser won't try typed pattern (name: Type)
        // because colon is the match arm body delimiter here
        self.in_match_arm_pattern = true;
        let pattern = self.parse_pattern()?;
        self.in_match_arm_pattern = false;

        // Handle `as Type` after pattern in match arms: case 'A' as u8:
        if self.check(&TokenKind::As) {
            self.advance(); // consume 'as'
            let _ty = self.parse_type()?; // consume the type
        }

        // Handle comma-separated or-patterns: case Int(_), Float(_), Bool(_):
        let pattern = if self.check(&TokenKind::Comma)
            && !self.check(&TokenKind::FatArrow)
        {
            let mut patterns = match pattern {
                Pattern::Or(ps) => ps,
                other => vec![other],
            };
            while self.check(&TokenKind::Comma) {
                self.advance();
                self.skip_whitespace_tokens();
                if self.check(&TokenKind::Colon)
                    || self.check(&TokenKind::FatArrow)
                    || self.check(&TokenKind::If)
                {
                    break;
                }
                self.in_match_arm_pattern = true;
                patterns.push(self.parse_single_pattern()?);
                self.in_match_arm_pattern = false;
            }
            if patterns.len() == 1 {
                patterns.into_iter().next().unwrap()
            } else {
                Pattern::Or(patterns)
            }
        } else {
            pattern
        };

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        let body = if self.check(&TokenKind::FatArrow) {
            self.advance();
            // Body can be single expression/statement or block
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let stmt = self.parse_item()?;
                Block {
                    span: self.previous.span,
                    statements: vec![stmt],
                }
            }
        } else if self.check(&TokenKind::Arrow) {
            // Arrow (->) as match arm delimiter (alternative syntax)
            self.advance();
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let stmt = self.parse_item()?;
                Block {
                    span: self.previous.span,
                    statements: vec![stmt],
                }
            }
        } else if self.check(&TokenKind::Colon) {
            self.advance();
            // Check if body is on same line (single expression/statement) or next line (block)
            if self.check(&TokenKind::Newline) {
                self.advance(); // consume newline before block
                if self.check(&TokenKind::Indent) {
                    self.parse_block_after_newline()?
                } else {
                    // Inside brackets: no Indent/Dedent tokens, parse statements until
                    // we see a match-arm-starting token or closing bracket
                    let block_start = self.current.span;
                    let mut statements = Vec::new();
                    while !self.is_at_end()
                        && !self.check(&TokenKind::Case)
                        && !self.check(&TokenKind::RParen)
                        && !self.check(&TokenKind::RBrace)
                        && !self.check(&TokenKind::RBracket)
                        && !self.check(&TokenKind::Dedent)
                    {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.is_at_end()
                            || self.check(&TokenKind::Case)
                            || self.check(&TokenKind::RParen)
                            || self.check(&TokenKind::RBrace)
                            || self.check(&TokenKind::RBracket)
                            || self.check(&TokenKind::Dedent)
                        {
                            break;
                        }
                        statements.push(self.parse_item()?);
                        if self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    Block {
                        span: Span::new(
                            block_start.start,
                            self.previous.span.end,
                            block_start.line,
                            block_start.column,
                        ),
                        statements,
                    }
                }
            } else {
                let stmt = self.parse_item()?;
                Block {
                    span: self.previous.span,
                    statements: vec![stmt],
                }
            }
        } else {
            return Err(ParseError::unexpected_token(
                "match arm",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        Ok(MatchArm {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            guard,
            body,
        })
    }

    // === Macro Definition ===

    /// Parse a macro definition: macro name!(params): body
    pub(crate) fn parse_macro_def(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Macro)?;

        let name = self.expect_identifier()?;
        // Optional `!` after macro name (macro name!(...) or macro name(...))
        if self.check(&TokenKind::Bang) {
            self.advance();
        }

        // Parse macro parameters
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) {
            let param = self.parse_macro_param()?;
            params.push(param);
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;

        // Optional return type specification: -> Type or -> (returns result: Type)
        if self.check(&TokenKind::Arrow) {
            self.advance(); // consume '->'
            if self.check(&TokenKind::LParen) {
                // Skip the entire parenthesized return spec: -> (returns result: Type)
                self.advance(); // consume '('
                let mut paren_depth = 1;
                while paren_depth > 0 && !self.check(&TokenKind::Eof) {
                    if self.check(&TokenKind::LParen) {
                        paren_depth += 1;
                    } else if self.check(&TokenKind::RParen) {
                        paren_depth -= 1;
                        if paren_depth == 0 {
                            break;
                        }
                    }
                    self.advance();
                }
                self.expect(&TokenKind::RParen)?;
            } else {
                // Simple return type: -> Type
                self.parse_type()?;
            }
        }

        self.expect(&TokenKind::Colon)?;

        // Parse macro body as a block
        let body = self.parse_block()?;

        let pattern = MacroPattern {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            params,
            body: MacroBody::Block(body),
        };

        Ok(Node::Macro(MacroDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            patterns: vec![pattern],
            visibility: Visibility::Private,
        }))
    }

    /// Parse a single macro parameter: $name or $name:ty
    pub(crate) fn parse_macro_param(&mut self) -> Result<MacroParam, ParseError> {
        if self.check(&TokenKind::Dollar) {
            self.advance();
            let name = self.expect_identifier()?;
            if self.check(&TokenKind::Colon) {
                self.advance();
                let kind = self.expect_identifier()?;
                match kind.as_str() {
                    "expr" => Ok(MacroParam::Expr(name)),
                    "ty" => Ok(MacroParam::Type(name)),
                    "ident" => Ok(MacroParam::Ident(name)),
                    _ => Ok(MacroParam::Expr(name)), // Default to expr
                }
            } else {
                Ok(MacroParam::Expr(name)) // Default: $x is expression capture
            }
        } else if self.check(&TokenKind::Ellipsis) {
            self.advance();
            if self.check(&TokenKind::Dollar) {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(MacroParam::Variadic {
                    name,
                    separator: None,
                })
            } else {
                Err(ParseError::unexpected_token(
                    "$ after ...",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        } else {
            // Could be a literal token match, or a Simple-style typed parameter: name: Type
            let lit = if let TokenKind::Identifier(name) = &self.current.kind {
                let name = name.clone();
                self.advance();
                name
            } else {
                let lexeme = self.current.lexeme.clone();
                self.advance();
                lexeme
            };
            // Check for Simple-style parameter: name: Type (treat as expression capture)
            if self.check(&TokenKind::Colon) {
                self.advance(); // consume ':'
                // Skip the type annotation (could be a path like Int, String, etc.)
                self.parse_type()?;
                Ok(MacroParam::Expr(lit))
            } else {
                Ok(MacroParam::Literal(lit))
            }
        }
    }

    // === Module System (Features #104-111) ===

    /// Parse a module path: crate.sys.http.router
    /// Returns the segments as a vector
    pub(crate) fn parse_module_path(&mut self) -> Result<ModulePath, ParseError> {
        let mut segments = Vec::new();

        // Handle string literal paths: import "types" or import "std/http/common"
        // The lexer turns "..." into FString([Literal(...)]) since double quotes are f-strings
        if let TokenKind::FString(parts) = &self.current.kind {
            if parts.len() == 1 {
                if let crate::token::FStringToken::Literal(path_str) = &parts[0] {
                    let path_str = path_str.clone();
                    self.advance();
                    // Split the string path by '/' to create segments
                    for seg in path_str.split('/') {
                        if !seg.is_empty() {
                            segments.push(seg.to_string());
                        }
                    }
                    return Ok(ModulePath::new(segments));
                }
            }
            // Empty f-string "" - treat as empty path
            if parts.is_empty() {
                self.advance();
                return Ok(ModulePath::new(vec![]));
            }
        }
        // Also handle RawString which uses r"..." syntax
        if let TokenKind::RawString(path_str) = &self.current.kind {
            let path_str = path_str.clone();
            self.advance();
            for seg in path_str.split('/') {
                if !seg.is_empty() {
                    segments.push(seg.to_string());
                }
            }
            return Ok(ModulePath::new(segments));
        }
        // Also handle String token for plain string imports
        if let TokenKind::String(path_str) = &self.current.kind {
            let path_str = path_str.clone();
            self.advance();
            for seg in path_str.split('/') {
                if !seg.is_empty() {
                    segments.push(seg.to_string());
                }
            }
            return Ok(ModulePath::new(segments));
        }

        // Handle relative path starting with '...' (e.g., ...monomorphize.note_sdn)
        if self.check(&TokenKind::Ellipsis) {
            self.advance();
            segments.push("...".to_string());
            segments.push(self.expect_path_segment()?);
        } else if self.check(&TokenKind::DoubleDot) {
            self.advance();
            segments.push("..".to_string());
            segments.push(self.expect_path_segment()?);
        } else if self.check(&TokenKind::Dot) {
            // Handle relative path starting with '.' (e.g., .definition, .note_sdn)
            self.advance();
            segments.push(".".to_string());
            segments.push(self.expect_path_segment()?);
        } else if self.check(&TokenKind::Crate) {
            // First segment (could be 'crate' keyword or identifier)
            self.advance();
            segments.push("crate".to_string());
        } else {
            // Use expect_path_segment to allow keywords like 'unit', 'test', etc.
            segments.push(self.expect_path_segment()?);
        }

        // Parse dot-separated, slash-separated, or ::-separated segments
        while self.check(&TokenKind::Dot)
            || self.check(&TokenKind::Slash)
            || self.check(&TokenKind::DoubleColon)
        {
            self.advance();

            // Check for glob: module.*
            if self.check(&TokenKind::Star) {
                break; // Stop, let caller handle *
            }

            // Check for group: module.{A, B}
            if self.check(&TokenKind::LBrace) {
                break; // Stop, let caller handle {}
            }

            // Use expect_path_segment to allow keywords as path segments
            segments.push(self.expect_path_segment()?);
        }

        Ok(ModulePath::new(segments))
    }

    /// Parse an import target: single item, alias, group, or glob
    /// Called after the module path is parsed
    pub(crate) fn parse_import_target(
        &mut self,
        last_segment: Option<String>,
    ) -> Result<ImportTarget, ParseError> {
        // Check for glob: *
        if self.check(&TokenKind::Star) {
            self.advance();
            return Ok(ImportTarget::Glob);
        }

        // Check for group: {A, B, C}
        if self.check(&TokenKind::LBrace) {
            self.advance();
            // Skip whitespace after opening brace (for multi-line import groups)
            self.skip_whitespace_tokens();
            let mut targets = Vec::new();

            while !self.check(&TokenKind::RBrace) {
                let name = self.expect_identifier()?;
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_identifier()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);

                // Skip whitespace after target
                self.skip_whitespace_tokens();

                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
                    // Skip whitespace after comma
                    self.skip_whitespace_tokens();
                }
            }
            self.expect(&TokenKind::RBrace)?;
            return Ok(ImportTarget::Group(targets));
        }

        // Single item (already parsed as last segment of path)
        if let Some(name) = last_segment {
            // Check for alias: as NewName
            if self.check(&TokenKind::As) {
                self.advance();
                let alias = self.expect_identifier()?;
                return Ok(ImportTarget::Aliased { name, alias });
            }
            return Ok(ImportTarget::Single(name));
        }

        Err(ParseError::unexpected_token(
            "import target",
            format!("{:?}", self.current.kind),
            self.current.span,
        ))
    }

    /// Parse use statement: use crate.module.Item
    /// use crate.module.{A, B}
    /// use crate.module.*
    /// use crate.module.Item as Alias
    pub(crate) fn parse_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Use)?;
        self.parse_use_or_import_body(start_span)
    }

    /// Parse `pub use X.Y.Z` as an export use statement
    pub(crate) fn parse_export_use_from_pub(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Use)?;
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::ExportUseStmt(ExportUseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse import statement (alias for use): import module.Item
    /// This is syntactic sugar for `use` - both work identically.
    pub(crate) fn parse_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Import)?;

        // Check for JavaScript-style: import X from "path" or import "path" as X
        // First check if first token is a string (import "types" or import "types" as X)
        if matches!(
            &self.current.kind,
            TokenKind::FString(_) | TokenKind::RawString(_) | TokenKind::String(_)
        ) {
            let path = self.parse_module_path()?;
            // Check for `as alias`
            let target = if self.check(&TokenKind::As) {
                self.advance();
                let alias_name = self.expect_identifier()?;
                ImportTarget::Aliased {
                    name: path.segments.last().cloned().unwrap_or_default(),
                    alias: alias_name,
                }
            } else {
                ImportTarget::Glob
            };
            return Ok(Node::UseStmt(UseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target,
            }));
        }

        // Check for: import Name from "path" or import Name from module.path
        // This is detected by parsing the first identifier, then checking for `from`
        let (path, target) = self.parse_use_path_and_target()?;
        if self.check(&TokenKind::From) {
            // JS-style: import Name from "path"
            self.advance();
            let from_path = self.parse_module_path()?;
            return Ok(Node::UseStmt(UseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: from_path,
                target,
            }));
        }

        // Standard use/import body
        // Check for comma-separated additional paths: use A.B, C.D, E.F
        if self.check(&TokenKind::Comma) {
            let mut targets = match target {
                ImportTarget::Single(name) => vec![ImportTarget::Single(name)],
                ImportTarget::Group(group) => group,
                other => vec![other],
            };
            let first_path = path;

            while self.check(&TokenKind::Comma) {
                self.advance();
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Newline) || self.is_at_end() {
                    break;
                }
                let (next_path, next_target) = self.parse_use_path_and_target()?;
                match next_target {
                    ImportTarget::Single(name) => targets.push(ImportTarget::Single(name)),
                    ImportTarget::Group(group) => targets.extend(group),
                    other => targets.push(other),
                }
                let _ = next_path;
            }

            return Ok(Node::UseStmt(UseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: first_path,
                target: ImportTarget::Group(targets),
            }));
        }

        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Common body for use/import statements
    /// Handles both single use: `use module.Item`
    /// and comma-separated: `use module.Item1, module.Item2`
    fn parse_use_or_import_body(&mut self, start_span: Span) -> Result<Node, ParseError> {
        let (path, target) = self.parse_use_path_and_target()?;

        // Check for comma-separated additional paths: use A.B, C.D, E.F
        if self.check(&TokenKind::Comma) {
            let mut targets = match target {
                ImportTarget::Single(name) => vec![ImportTarget::Single(name)],
                ImportTarget::Group(group) => group,
                other => vec![other],
            };
            let first_path = path;

            while self.check(&TokenKind::Comma) {
                self.advance();
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Newline) || self.is_at_end() {
                    break;
                }
                // Parse next use path
                let (next_path, next_target) = self.parse_use_path_and_target()?;
                // Flatten the target into our group
                match next_target {
                    ImportTarget::Single(name) => targets.push(ImportTarget::Single(name)),
                    ImportTarget::Group(group) => targets.extend(group),
                    other => targets.push(other),
                }
                let _ = next_path; // Each path may differ; we use first as primary
            }

            return Ok(Node::UseStmt(UseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: first_path,
                target: ImportTarget::Group(targets),
            }));
        }

        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse mod declaration: mod name or pub mod name
    pub(crate) fn parse_mod(
        &mut self,
        visibility: Visibility,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mod)?;
        let name = self.expect_identifier()?;
        // Check for module with body: `module name:\n    body`
        if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            // Parse the module body as a block
            let _body = self.parse_block_or_inline()?;
            // Still return ModDecl (the body contents are parsed but not stored in AST)
        }
        Ok(Node::ModDecl(ModDecl {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            visibility,
            attributes,
        }))
    }

    /// Parse common use: common use crate.module.*
    pub(crate) fn parse_common_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Common)?;
        self.expect(&TokenKind::Use)?;
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::CommonUseStmt(CommonUseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse export statement:
    /// - `export use router.Router` - re-export from module
    /// - `export NAME1, NAME2, ...` - export local names
    pub(crate) fn parse_export_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Export)?;

        // Check if this is `export class/struct/fn/trait/enum/...` - definition with public visibility
        match &self.current.kind {
            TokenKind::Class => {
                let mut node = self.parse_class()?;
                if let Node::Class(ref mut c) = node { c.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct()?;
                if let Node::Struct(ref mut s) = node { s.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Fn => {
                let mut node = self.parse_function()?;
                if let Node::Function(ref mut f) = node { f.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function()?;
                if let Node::Function(ref mut f) = node { f.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum()?;
                if let Node::Enum(ref mut e) = node { e.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Union => {
                let mut node = self.parse_union()?;
                if let Node::Enum(ref mut e) = node { e.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait()?;
                if let Node::Trait(ref mut t) = node { t.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Actor => {
                let mut node = self.parse_actor()?;
                if let Node::Actor(ref mut a) = node { a.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Const => {
                let mut node = self.parse_const()?;
                if let Node::Const(ref mut c) = node { c.visibility = Visibility::Public; }
                return Ok(node);
            }
            TokenKind::Let => {
                let mut node = self.parse_let()?;
                if let Node::Let(ref mut l) = node { l.mutability = Mutability::Immutable; }
                return Ok(node);
            }
            TokenKind::Var => {
                let node = self.parse_var()?;
                return Ok(node);
            }
            TokenKind::Type => {
                return self.parse_type_alias();
            }
            TokenKind::Extern => {
                return self.parse_extern();
            }
            TokenKind::Macro => {
                return self.parse_macro_def();
            }
            TokenKind::Newline | TokenKind::Eof => {
                // Bare `export` on its own line - treat as export-all
                return Ok(Node::ExportUseStmt(ExportUseStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    path: ModulePath::new(vec![]),
                    target: ImportTarget::Glob,
                }));
            }
            _ => {}
        }

        // Check if this is `export use ...` or `export NAME, ...`
        if self.check(&TokenKind::Use) {
            self.expect(&TokenKind::Use)?;
            let (path, target) = self.parse_use_path_and_target()?;
            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target,
            }))
        } else if self.check(&TokenKind::Star) {
            // export * — glob export of all names
            // export * from module.path — glob re-export from module
            self.advance();
            let path = if self.check(&TokenKind::From) {
                self.advance();
                self.parse_module_path()?
            } else {
                ModulePath::new(vec![])
            };
            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target: ImportTarget::Glob,
            }))
        } else if self.check(&TokenKind::LParen) {
            // export () - unit/empty export
            self.advance();
            self.expect(&TokenKind::RParen)?;
            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: ModulePath::new(vec![]),
                target: ImportTarget::Group(vec![]),
            }))
        } else if self.check(&TokenKind::LBrace) {
            // export { Name1, Name2 } or export { Name1, Name2 } from module.path
            self.advance();
            self.skip_whitespace_tokens();
            let mut names = Vec::new();
            while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                let name = self.expect_identifier()?;
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_identifier()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                names.push(target);
                self.skip_whitespace_tokens();
                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
                    self.skip_whitespace_tokens();
                }
            }
            self.expect(&TokenKind::RBrace)?;
            let path = if self.check(&TokenKind::From) {
                self.advance();
                self.parse_module_path()?
            } else {
                ModulePath::new(vec![])
            };
            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target: ImportTarget::Group(names),
            }))
        } else {
            // Parse first name (might be a dotted path like `export resolution.*`)
            let first_name = self.expect_identifier()?;

            // Check for export assignment: export name = expr
            if self.check(&TokenKind::Assign) {
                self.advance(); // consume '='
                let _value_expr = self.parse_expression()?;
                // Treat as an export of a single name (the assignment is a re-export alias)
                return Ok(Node::ExportUseStmt(ExportUseStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    path: ModulePath::new(vec![]),
                    target: ImportTarget::Single(first_name),
                }));
            }

            // Check for dotted path: export resolution.*
            if self.check(&TokenKind::Dot) {
                self.advance();
                if self.check(&TokenKind::Star) {
                    // export NAME.*  -> glob re-export
                    self.advance();
                    return Ok(Node::ExportUseStmt(ExportUseStmt {
                        span: Span::new(
                            start_span.start,
                            self.previous.span.end,
                            start_span.line,
                            start_span.column,
                        ),
                        path: ModulePath::new(vec![first_name]),
                        target: ImportTarget::Glob,
                    }));
                } else if self.check(&TokenKind::LBrace) {
                    // export NAME.{A, B, C}
                    self.advance();
                    // Skip whitespace after opening brace (for multi-line exports)
                    self.skip_whitespace_tokens();
                    let mut inner = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        inner.push(ImportTarget::Single(self.expect_identifier()?));
                        // Skip whitespace after name
                        self.skip_whitespace_tokens();
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                            // Skip whitespace after comma
                            self.skip_whitespace_tokens();
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Node::ExportUseStmt(ExportUseStmt {
                        span: Span::new(
                            start_span.start,
                            self.previous.span.end,
                            start_span.line,
                            start_span.column,
                        ),
                        path: ModulePath::new(vec![first_name]),
                        target: ImportTarget::Group(inner),
                    }));
                } else {
                    // export A.B — continue as dotted path
                    // Also handles: export A.B, A.C (comma-separated dotted paths)
                    let mut segments = vec![first_name];
                    segments.push(self.expect_identifier()?);
                    while self.check(&TokenKind::Dot) {
                        self.advance();
                        if self.check(&TokenKind::Star) {
                            self.advance();
                            return Ok(Node::ExportUseStmt(ExportUseStmt {
                                span: Span::new(
                                    start_span.start,
                                    self.previous.span.end,
                                    start_span.line,
                                    start_span.column,
                                ),
                                path: ModulePath::new(segments),
                                target: ImportTarget::Glob,
                            }));
                        }
                        segments.push(self.expect_identifier()?);
                    }
                    let target_name = segments.pop().unwrap();
                    let path = ModulePath::new(segments);

                    // Check for comma-separated additional dotted paths
                    if self.check(&TokenKind::Comma) {
                        let mut targets = vec![ImportTarget::Single(target_name)];
                        let mut paths = vec![path.clone()];
                        while self.check(&TokenKind::Comma) {
                            self.advance();
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            if self.check(&TokenKind::Newline) || self.is_at_end() {
                                break;
                            }
                            // Parse next dotted path segment
                            let next_name = self.expect_identifier()?;
                            if self.check(&TokenKind::Dot) {
                                let mut next_segs = vec![next_name];
                                while self.check(&TokenKind::Dot) {
                                    self.advance();
                                    next_segs.push(self.expect_identifier()?);
                                }
                                let tgt = next_segs.pop().unwrap();
                                targets.push(ImportTarget::Single(tgt));
                                paths.push(ModulePath::new(next_segs));
                            } else {
                                targets.push(ImportTarget::Single(next_name));
                                paths.push(ModulePath::new(vec![]));
                            }
                        }
                        // Use the first path as the common path (even if each has different paths,
                        // this is a simplification that preserves parsing success)
                        return Ok(Node::ExportUseStmt(ExportUseStmt {
                            span: Span::new(
                                start_span.start,
                                self.previous.span.end,
                                start_span.line,
                                start_span.column,
                            ),
                            path: paths.into_iter().next().unwrap_or_else(|| ModulePath::new(vec![])),
                            target: ImportTarget::Group(targets),
                        }));
                    }

                    return Ok(Node::ExportUseStmt(ExportUseStmt {
                        span: Span::new(
                            start_span.start,
                            self.previous.span.end,
                            start_span.line,
                            start_span.column,
                        ),
                        path,
                        target: ImportTarget::Single(target_name),
                    }));
                }
            }

            // `export NAME1, NAME2, ...` — collect names as group import target
            // Handle `?` suffix on names (e.g., `export iter_empty?, iter_single?`)
            let mut first_name = first_name;
            if self.check(&TokenKind::Question) {
                self.advance();
                first_name = format!("{}?", first_name);
            }
            let mut names = vec![first_name];
            while self.check(&TokenKind::Comma) {
                self.advance();
                // Skip whitespace tokens including Newline, Indent, Dedent for multi-line exports
                while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
                    if self.check(&TokenKind::Indent) {
                        self.advance();
                        self.lexer.indent_stack.pop();
                    } else {
                        self.advance();
                    }
                }
                if self.check(&TokenKind::Newline) || self.is_at_end() {
                    break;
                }
                let mut name = self.expect_identifier()?;
                // Handle `?` suffix (e.g., `iter_empty?`)
                if self.check(&TokenKind::Question) {
                    self.advance();
                    name = format!("{}?", name);
                }
                names.push(name);
            }

            let targets: Vec<ImportTarget> = names
                .into_iter()
                .map(|n| ImportTarget::Single(n))
                .collect();

            // Check for 'from .module_path' after names
            let path = if self.check(&TokenKind::From) {
                self.advance();
                self.parse_module_path()?
            } else {
                ModulePath::new(vec![])
            };

            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target: ImportTarget::Group(targets),
            }))
        }
    }

    /// Parse from-import: `from module_path import {Name1, Name2}` or `from module_path import {*}`
    /// Translates to equivalent use statement: `use module_path.{Name1, Name2}`
    pub(crate) fn parse_from_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::From)?;

        // Parse module path (dot-separated identifiers)
        let path = self.parse_module_path()?;

        // Expect 'import'
        self.expect(&TokenKind::Import)?;

        // Parse import target: {Name1, Name2} or {*} or Name
        let target = if self.check(&TokenKind::LBrace) {
            self.advance();
            if self.check(&TokenKind::Star) {
                // from X import {*}
                self.advance();
                self.expect(&TokenKind::RBrace)?;
                ImportTarget::Glob
            } else {
                // from X import {A, B, C} or {A as B, C}
                // Skip whitespace after opening brace (for multi-line imports)
                self.skip_whitespace_tokens();
                let mut names = Vec::new();
                while !self.check(&TokenKind::RBrace) {
                    let name = self.expect_identifier()?;
                    let target = if self.check(&TokenKind::As) {
                        self.advance();
                        let alias = self.expect_identifier()?;
                        ImportTarget::Aliased { name, alias }
                    } else {
                        ImportTarget::Single(name)
                    };
                    names.push(target);
                    // Skip whitespace after target
                    self.skip_whitespace_tokens();
                    if !self.check(&TokenKind::RBrace) {
                        self.expect(&TokenKind::Comma)?;
                        // Skip whitespace after comma
                        self.skip_whitespace_tokens();
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                ImportTarget::Group(names)
            }
        } else if self.check(&TokenKind::Star) {
            // from X import *
            self.advance();
            ImportTarget::Glob
        } else {
            // from X import Name or from X import Name1, Name2, ...
            let first_name = self.expect_identifier()?;
            if self.check(&TokenKind::Comma) {
                // from X import A, B, C
                let mut names = vec![ImportTarget::Single(first_name)];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    self.skip_whitespace_tokens();
                    if self.check(&TokenKind::Newline) || self.check(&TokenKind::Eof) {
                        break; // trailing comma
                    }
                    let name = self.expect_identifier()?;
                    let target = if self.check(&TokenKind::As) {
                        self.advance();
                        let alias = self.expect_identifier()?;
                        ImportTarget::Aliased { name, alias }
                    } else {
                        ImportTarget::Single(name)
                    };
                    names.push(target);
                }
                ImportTarget::Group(names)
            } else if self.check(&TokenKind::As) {
                self.advance();
                let alias = self.expect_identifier()?;
                ImportTarget::Aliased {
                    name: first_name,
                    alias,
                }
            } else {
                ImportTarget::Single(first_name)
            }
        };

        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse auto import: auto import router.route
    pub(crate) fn parse_auto_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Auto)?;
        self.expect(&TokenKind::Import)?;

        let path = self.parse_module_path()?;

        // Last segment is the macro name
        let mut segments = path.segments;
        let macro_name = segments.pop().unwrap_or_default();

        Ok(Node::AutoImportStmt(AutoImportStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path: ModulePath::new(segments),
            macro_name,
        }))
    }
}
