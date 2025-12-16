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
            Ok(Some(self.parse_expression()?))
        } else {
            Ok(None)
        }
    }

    /// Helper to parse name, type annotation, and assigned value for const/static
    fn parse_named_value(&mut self) -> Result<(String, Option<Type>, Expr), ParseError> {
        let name = self.expect_identifier()?;
        let ty = self.parse_optional_type_annotation()?;
        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expression()?;
        Ok((name, ty, value))
    }

    /// Parse optional let-pattern syntax: `let PATTERN =`
    /// Used by if-let and while-let constructs
    fn parse_optional_let_pattern(&mut self) -> Result<(Option<Pattern>, Expr), ParseError> {
        if self.check(&TokenKind::Let) {
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

        if self.check(&TokenKind::Star) || self.check(&TokenKind::LBrace) {
            let target = self.parse_import_target(None)?;
            Ok((path, target))
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

        let name = self.expect_identifier()?;

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

    pub(crate) fn parse_extern(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Extern)?;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
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

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let then_block = self.parse_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let elif_condition = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_block()?;
            elif_branches.push((elif_condition, elif_block));
        }

        let else_block = if self.check(&TokenKind::Else) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            Some(self.parse_block()?)
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

        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

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

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

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
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut arms = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
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
    }

    pub(crate) fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;
        if self.check(&TokenKind::Case) {
            self.advance();
        }
        let pattern = self.parse_pattern()?;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        let body = if self.check(&TokenKind::FatArrow) {
            self.advance();
            // Body can be single expression or block
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else if self.check(&TokenKind::Colon) {
            self.advance();
            self.parse_block()?
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
        self.expect(&TokenKind::Bang)?;

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
            // Literal token that must match
            let lit = if let TokenKind::Identifier(name) = &self.current.kind {
                let name = name.clone();
                self.advance();
                name
            } else {
                let lexeme = self.current.lexeme.clone();
                self.advance();
                lexeme
            };
            Ok(MacroParam::Literal(lit))
        }
    }

    // === Module System (Features #104-111) ===

    /// Parse a module path: crate.sys.http.router
    /// Returns the segments as a vector
    pub(crate) fn parse_module_path(&mut self) -> Result<ModulePath, ParseError> {
        let mut segments = Vec::new();

        // First segment (could be 'crate' keyword or identifier)
        if self.check(&TokenKind::Crate) {
            self.advance();
            segments.push("crate".to_string());
        } else {
            // Use expect_path_segment to allow keywords like 'unit', 'test', etc.
            segments.push(self.expect_path_segment()?);
        }

        // Parse dot-separated segments
        while self.check(&TokenKind::Dot) {
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

                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
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

    /// Parse import statement (alias for use): import module.Item
    /// This is syntactic sugar for `use` - both work identically.
    pub(crate) fn parse_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Import)?;
        self.parse_use_or_import_body(start_span)
    }

    /// Common body for use/import statements
    fn parse_use_or_import_body(&mut self, start_span: Span) -> Result<Node, ParseError> {
        let (path, target) = self.parse_use_path_and_target()?;
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

    /// Parse export use: export use router.Router
    pub(crate) fn parse_export_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Export)?;
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

    /// Parse requires capabilities statement: requires [pure, io, net]
    ///
    /// This declares the capabilities allowed in the current module.
    /// Must appear at the top of __init__.spl files.
    pub(crate) fn parse_requires_capabilities(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Requires)?;
        self.expect(&TokenKind::LBracket)?;

        let mut capabilities = Vec::new();

        // Parse capability list
        if !self.check(&TokenKind::RBracket) {
            loop {
                // Parse capability name as identifier
                let cap_name = self.expect_identifier()?;

                // Convert to Capability enum
                let capability = Capability::from_name(&cap_name).ok_or_else(|| {
                    ParseError::syntax_error_with_span(
                        format!(
                            "unknown capability '{}'. Valid capabilities: pure, io, net, fs, unsafe, gc",
                            cap_name
                        ),
                        self.previous.span,
                    )
                })?;

                capabilities.push(capability);

                // Check for comma or end
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Allow trailing comma
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RBracket)?;

        Ok(Node::RequiresCapabilities(RequiresCapabilitiesStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            capabilities,
        }))
    }
}
