//! Variable declarations parsing (let, const, static, type, unit, extern, handle_pool)

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl Parser<'_> {
    // === Variable Declarations ===

    pub(crate) fn parse_mut_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mut)?;
        self.expect(&TokenKind::Let)?;
        self.parse_let_impl(start_span, Mutability::Mutable, StorageClass::Auto, false)
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
        self.parse_let_impl(start_span, mutability, StorageClass::Auto, false)
    }

    /// Parse val: `val name = value` (immutable variable, Scala-style)
    pub(crate) fn parse_val(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Val)?;
        self.parse_let_impl(start_span, Mutability::Immutable, StorageClass::Auto, false)
    }

    /// Parse var: `var name = value` (mutable variable, Scala-style)
    pub(crate) fn parse_var(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Var)?;

        // Check for common mistake: `var fn` instead of `me` for mutable methods
        if self.check(&TokenKind::Fn) {
            return Err(ParseError::syntax_error_with_span(
                "Use `me` keyword instead of `var fn` for mutable methods. Example: `me update(x: i32):` instead of `var fn update(x: i32):`",
                self.current.span,
            ));
        }

        self.parse_let_impl(start_span, Mutability::Mutable, StorageClass::Auto, false)
    }

    /// Parse shared let: `shared let name: [T; N]`
    /// GPU work-group shared memory declaration
    pub(crate) fn parse_shared_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Shared)?;
        self.expect(&TokenKind::Let)?;
        // Shared memory is always mutable (work-group accessible)
        self.parse_let_impl(start_span, Mutability::Mutable, StorageClass::Shared, false)
    }

    /// Parse ghost let: `ghost let name: Type = value`
    /// Verification-only variable, erased at runtime
    pub(crate) fn parse_ghost_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Ghost)?;
        self.expect(&TokenKind::Let)?;
        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };
        self.parse_let_impl(start_span, mutability, StorageClass::Auto, true)
    }

    /// Parse wildcard suspension: `_ ~= expr`
    /// Evaluates expr with await and discards the result
    pub(crate) fn parse_wildcard_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Underscore)?;
        self.expect(&TokenKind::TildeAssign)?;
        let value = self.parse_expression()?;

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern: Pattern::Wildcard,
            ty: None,
            value: Some(value),
            mutability: Mutability::Immutable,
            storage_class: StorageClass::Auto,
            is_ghost: false,
            is_suspend: true,
        }))
    }

    fn parse_let_impl(
        &mut self,
        start_span: Span,
        mutability: Mutability,
        storage_class: StorageClass,
        is_ghost: bool,
    ) -> Result<Node, ParseError> {
        let mut pattern = self.parse_pattern()?;
        let ty = self.parse_optional_type_annotation()?;
        let (value, is_suspend) = self.parse_optional_assignment_with_suspend()?;

        // Wrap pattern in Pattern::Typed if there's a type annotation
        // This provides the typed pattern that tests and code expect
        if let Some(type_annotation) = ty {
            pattern = Pattern::Typed {
                pattern: Box::new(pattern),
                ty: type_annotation,
            };
        }

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            ty: None, // Type is now in the Pattern::Typed wrapper
            value,
            mutability,
            storage_class,
            is_ghost,
            is_suspend,
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

    /// Parse optional assignment `= expr` or `~= expr` (suspension assignment)
    /// Returns (Option<Expr>, bool) where bool indicates if this is a suspension assignment
    fn parse_optional_assignment_with_suspend(&mut self) -> Result<(Option<Expr>, bool), ParseError> {
        if self.check(&TokenKind::Assign) {
            self.advance();
            Ok((Some(self.parse_expression()?), false))
        } else if self.check(&TokenKind::TildeAssign) {
            self.advance();
            Ok((Some(self.parse_expression()?), true))
        } else {
            Ok((None, false))
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
    pub(crate) fn parse_optional_let_pattern(&mut self) -> Result<(Option<Pattern>, Expr), ParseError> {
        if self.check(&TokenKind::Let) || self.check(&TokenKind::Val) {
            self.advance(); // consume let or val
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
    /// Also supports bare glob (use *, export use *)
    pub(crate) fn parse_use_path_and_target(&mut self) -> Result<(ModulePath, ImportTarget), ParseError> {
        // Handle bare * or {A, B} without module path
        // This supports: export use *, use *, export use {A, B}
        if self.check(&TokenKind::Star) || self.check(&TokenKind::LBrace) {
            let target = self.parse_import_target(None)?;
            return Ok((ModulePath::new(Vec::new()), target));
        }

        let path = self.parse_module_path()?;

        // Check for Rust-style :: before { or *
        if self.check(&TokenKind::DoubleColon) {
            self.advance(); // consume ::
        }

        if self.check(&TokenKind::Star) || self.check(&TokenKind::LBrace) {
            let target = self.parse_import_target(None)?;
            Ok((path, target))
        } else {
            let mut segments = path.segments.clone();

            // Special case: bare module import (use core, import torch, etc.)
            // If we have only one segment and we're at a statement boundary (newline/EOF),
            // import everything from that module
            if segments.len() == 1 && (self.check(&TokenKind::Newline) || self.is_at_end()) {
                // Import entire module: use core -> import * from core
                return Ok((path, ImportTarget::Glob));
            }

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

    /// Parse unit definition: standalone, family, or compound
    /// Standalone: `unit UserId: i64 as uid`
    /// Family: `unit length(base: f64): m = 1.0, km = 1000.0`
    /// Family with arithmetic: `unit length(base: f64): m = 1.0, km = 1000.0: allow add(length) -> length`
    /// Compound: `unit velocity = length / time`
    pub(crate) fn parse_unit(&mut self) -> Result<Node, ParseError> {
        use crate::ast::{CompoundUnitDef, UnitFamilyDef};

        let start_span = self.current.span;
        self.expect(&TokenKind::Unit)?;

        let name = self.expect_identifier()?;

        // Check if this is a compound unit: unit name = unit_expr
        if self.check(&TokenKind::Assign) {
            self.advance(); // consume '='
            let expr = self.parse_unit_expr()?;

            // Check for optional arithmetic block
            let arithmetic = if self.check(&TokenKind::Colon) {
                self.advance(); // consume ':'
                Some(self.parse_unit_arithmetic_block()?)
            } else {
                None
            };

            return Ok(Node::CompoundUnit(CompoundUnitDef {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                name,
                expr,
                arithmetic,
                visibility: Visibility::Private,
            }));
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
            let mut arithmetic = None;

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

                // Check for arithmetic block after single-line variants
                // unit length(base: f64): m = 1.0, km = 1000.0:
                if self.check(&TokenKind::Colon) {
                    self.advance(); // consume ':'
                    arithmetic = Some(self.parse_unit_arithmetic_block()?);
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
                arithmetic,
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

    /// Parse unit expression for compound units: length / time, mass * acceleration, time^2
    fn parse_unit_expr(&mut self) -> Result<UnitExpr, ParseError> {
        let mut left = self.parse_unit_term()?;

        while self.check(&TokenKind::Star) || self.check(&TokenKind::Slash) {
            let op = self.current.kind.clone();
            self.advance();
            let right = self.parse_unit_term()?;

            left = match op {
                TokenKind::Star => UnitExpr::Mul(Box::new(left), Box::new(right)),
                TokenKind::Slash => UnitExpr::Div(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
        }

        Ok(left)
    }

    /// Parse a unit term: identifier or identifier^exponent
    fn parse_unit_term(&mut self) -> Result<UnitExpr, ParseError> {
        let name = self.expect_identifier()?;
        let base = UnitExpr::Base(name);

        // Check for power: time^2
        if self.check(&TokenKind::Caret) {
            self.advance();
            // Parse integer exponent (can be negative)
            let negative = if self.check(&TokenKind::Minus) {
                self.advance();
                true
            } else {
                false
            };

            let exp = match &self.current.kind {
                TokenKind::Integer(n) => {
                    let val = *n as i32;
                    self.advance();
                    if negative {
                        -val
                    } else {
                        val
                    }
                }
                _ => {
                    return Err(ParseError::syntax_error_with_span(
                        "Expected integer exponent after '^'",
                        self.current.span,
                    ));
                }
            };

            Ok(UnitExpr::Pow(Box::new(base), exp))
        } else {
            Ok(base)
        }
    }

    /// Parse unit arithmetic block: allow rules, repr constraints, and custom functions
    fn parse_unit_arithmetic_block(&mut self) -> Result<UnitArithmetic, ParseError> {
        let mut binary_rules = Vec::new();
        let mut unary_rules = Vec::new();
        let mut custom_fns = Vec::new();
        let mut allowed_reprs = Vec::new();

        // Skip newline if present
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Expect indented block
        if !self.check(&TokenKind::Indent) {
            return Err(ParseError::syntax_error_with_span(
                "Expected indented block for unit arithmetic rules",
                self.current.span,
            ));
        }
        self.advance(); // consume indent

        // Parse rules until dedent
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Parse rule: 'allow', 'repr', or 'fn'
            // Note: 'allow' can be either an identifier or the Allow keyword
            if matches!(&self.current.kind, TokenKind::Identifier { name: s, .. } if s == "allow")
                || self.check(&TokenKind::Allow)
            {
                self.advance(); // consume 'allow'
                self.parse_arithmetic_rule(&mut binary_rules, &mut unary_rules)?;
            } else if self.check(&TokenKind::Repr) {
                // Parse repr: u8, i12, f32, ...
                self.advance(); // consume 'repr'
                self.expect(&TokenKind::Colon)?;
                allowed_reprs = self.parse_repr_list()?;
            } else if self.check(&TokenKind::Fn) {
                // Parse custom function
                let func = self.parse_function()?;
                if let Node::Function(f) = func {
                    custom_fns.push(f);
                }
            } else {
                return Err(ParseError::syntax_error_with_span(
                    format!(
                        "Expected 'allow', 'repr', or 'fn' in unit arithmetic block, got {:?}",
                        self.current.kind
                    ),
                    self.current.span,
                ));
            }

            // Skip newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume dedent
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(UnitArithmetic {
            binary_rules,
            unary_rules,
            custom_fns,
            allowed_reprs,
        })
    }

    /// Parse a list of repr types: u8, i12, f32, ...
    fn parse_repr_list(&mut self) -> Result<Vec<ReprType>, ParseError> {
        let mut reprs = Vec::new();

        // Parse first repr type
        reprs.push(self.parse_repr_type()?);

        // Parse additional repr types separated by commas
        while self.check(&TokenKind::Comma) {
            self.advance(); // consume ','
            reprs.push(self.parse_repr_type()?);
        }

        Ok(reprs)
    }

    /// Parse a single repr type: u8, i12, f32, etc.
    fn parse_repr_type(&mut self) -> Result<ReprType, ParseError> {
        match &self.current.kind {
            TokenKind::Identifier { name: s, .. } => {
                let s = s.clone();
                if let Some(repr) = ReprType::from_str(&s) {
                    self.advance();
                    Ok(repr)
                } else {
                    Err(ParseError::syntax_error_with_span(
                        format!("Invalid repr type '{}'. Expected format: u8, i12, f32, etc.", s),
                        self.current.span,
                    ))
                }
            }
            _ => Err(ParseError::syntax_error_with_span(
                format!("Expected repr type (u8, i12, f32, etc.), got {:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse an arithmetic rule: binary or unary
    /// Binary: add(type) -> result_type
    /// Unary: neg -> result_type
    fn parse_arithmetic_rule(
        &mut self,
        binary_rules: &mut Vec<BinaryArithmeticRule>,
        unary_rules: &mut Vec<UnaryArithmeticRule>,
    ) -> Result<(), ParseError> {
        // Parse operation name
        let op_name = self.expect_identifier()?;

        // Check if this is a binary op (has parentheses) or unary (just ->)
        if self.check(&TokenKind::LParen) {
            // Binary operation: add(type) -> result
            self.advance(); // consume '('
            let operand_type = self.parse_type()?;
            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Arrow)?;
            let result_type = self.parse_type()?;

            let op = match op_name.as_str() {
                "add" => BinaryArithmeticOp::Add,
                "sub" => BinaryArithmeticOp::Sub,
                "mul" => BinaryArithmeticOp::Mul,
                "div" => BinaryArithmeticOp::Div,
                "mod" => BinaryArithmeticOp::Mod,
                _ => {
                    return Err(ParseError::syntax_error_with_span(
                        format!(
                            "Unknown binary arithmetic operation '{}'. Expected: add, sub, mul, div, mod",
                            op_name
                        ),
                        self.previous.span,
                    ));
                }
            };

            binary_rules.push(BinaryArithmeticRule {
                op,
                operand_type,
                result_type,
            });
        } else {
            // Unary operation: neg -> result
            self.expect(&TokenKind::Arrow)?;
            let result_type = self.parse_type()?;

            let op = match op_name.as_str() {
                "neg" => UnaryArithmeticOp::Neg,
                "abs" => UnaryArithmeticOp::Abs,
                _ => {
                    return Err(ParseError::syntax_error_with_span(
                        format!("Unknown unary arithmetic operation '{}'. Expected: neg, abs", op_name),
                        self.previous.span,
                    ));
                }
            };

            unary_rules.push(UnaryArithmeticRule { op, result_type });
        }

        Ok(())
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

    /// Parse handle_pool declaration:
    /// ```simple
    /// handle_pool Enemy:
    ///     capacity: 1024
    /// ```
    /// or inline: `handle_pool Enemy`
    pub(crate) fn parse_handle_pool(&mut self) -> Result<Node, ParseError> {
        use crate::ast::HandlePoolDef;

        let start_span = self.current.span;
        self.expect(&TokenKind::HandlePool)?;

        // Expect a type name (PascalCase identifier)
        let type_name = self.expect_identifier()?;

        let mut capacity = None;

        // Check for optional block with capacity
        if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'

            // Skip newline and expect indented block
            if self.check(&TokenKind::Newline) {
                self.advance();
                if self.check(&TokenKind::Indent) {
                    self.advance();

                    // Parse fields in block
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        // Skip newlines
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) {
                            break;
                        }

                        // Expect "capacity: N"
                        let field_name = self.expect_identifier()?;
                        self.expect(&TokenKind::Colon)?;

                        if field_name == "capacity" {
                            if let TokenKind::Integer(n) = &self.current.kind {
                                capacity = Some(*n as u64);
                                self.advance();
                            } else {
                                return Err(ParseError::syntax_error_with_span(
                                    "Expected integer for capacity".to_string(),
                                    self.current.span,
                                ));
                            }
                        } else {
                            return Err(ParseError::syntax_error_with_span(
                                format!("Unknown handle_pool field '{}', expected 'capacity'", field_name),
                                self.previous.span,
                            ));
                        }

                        // Skip newline after field
                        if self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }

                    // Consume dedent
                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                }
            }
        }

        Ok(Node::HandlePool(HandlePoolDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            type_name,
            capacity,
            visibility: Visibility::Private,
        }))
    }
}
