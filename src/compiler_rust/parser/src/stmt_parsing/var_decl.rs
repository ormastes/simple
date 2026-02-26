//! Variable declarations parsing (let, const, static, type, unit, extern, handle_pool)

use crate::ast::*;
use crate::error::ParseError;
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
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

        // Deprecated `var fn` syntax - emit warning and parse as mutable function
        if self.check(&TokenKind::Fn) {
            use crate::error_recovery::{ErrorHint, ErrorHintLevel};
            let warning = ErrorHint {
                level: ErrorHintLevel::Warning,
                message: "Deprecated: `var fn` syntax".to_string(),
                span: start_span,
                suggestion: Some("Replace `var fn method()` with `me method()`".to_string()),
                help: None,
            };
            self.error_hints.push(warning);
            // Parse as mutable function
            let mut node = self.parse_function()?;
            if let Node::Function(ref mut f) = node {
                f.is_me_method = true;
            }
            return Ok(node);
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

    /// Parse wildcard assignment: `_ ~= expr` (suspend) or `_ = expr` (discard)
    /// Evaluates expr (optionally with await) and discards the result
    pub(crate) fn parse_wildcard_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Underscore)?;

        // Accept both ~= (suspend) and = (discard)
        let is_suspend = if self.check(&TokenKind::TildeAssign) {
            self.advance();
            true
        } else if self.check(&TokenKind::Assign) {
            self.advance();
            false
        } else {
            return Err(ParseError::unexpected_token(
                "= or ~=",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

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
            is_suspend,
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
    /// Supports continuation on next line: `val x = \n    expr`
    fn parse_optional_assignment_with_suspend(&mut self) -> Result<(Option<Expr>, bool), ParseError> {
        if self.check(&TokenKind::Assign) {
            self.advance();
            // Skip newlines after = to allow continuation on next line
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            // Track if we consumed an indent (need to consume matching dedent)
            let consumed_indent = if self.check(&TokenKind::Indent) {
                self.advance();
                true
            } else {
                false
            };
            let mut expr = self.parse_expression()?;
            // Support no-paren calls in assignment: val x = double 5
            expr = self.parse_with_no_paren_calls(expr)?;
            // Consume matching dedent if we consumed an indent
            if consumed_indent {
                // Skip newlines before dedent
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }
            }
            Ok((Some(expr), false))
        } else if self.check(&TokenKind::TildeAssign) {
            self.advance();
            // Skip newlines after ~= to allow continuation on next line
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            // Track if we consumed an indent (need to consume matching dedent)
            let consumed_indent = if self.check(&TokenKind::Indent) {
                self.advance();
                true
            } else {
                false
            };
            let mut expr = self.parse_expression()?;
            // Support no-paren calls in suspend assignment: val x ~= double 5
            expr = self.parse_with_no_paren_calls(expr)?;
            // Consume matching dedent if we consumed an indent
            if consumed_indent {
                // Skip newlines before dedent
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }
            }
            Ok((Some(expr), true))
        } else {
            Ok((None, false))
        }
    }

    /// Parse optional assignment `= expr`
    /// Supports continuation on next line: `val x = \n    expr`
    fn parse_optional_assignment(&mut self) -> Result<Option<Expr>, ParseError> {
        if self.check(&TokenKind::Assign) {
            self.advance();
            // Skip newlines after = to allow continuation on next line
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            // Track if we consumed an indent (need to consume matching dedent)
            let consumed_indent = if self.check(&TokenKind::Indent) {
                self.advance();
                true
            } else {
                false
            };
            let expr = self.parse_expression()?;
            // Consume matching dedent if we consumed an indent
            if consumed_indent {
                // Skip newlines before dedent
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }
            }
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// Helper to parse name, type annotation, and assigned value for const/static
    /// Supports continuation on next line: `const X = \n    expr`
    fn parse_named_value(&mut self) -> Result<(String, Option<Type>, Expr), ParseError> {
        let name = self.expect_identifier()?;
        let ty = self.parse_optional_type_annotation()?;
        self.expect(&TokenKind::Assign)?;
        // Skip newlines after = to allow continuation on next line
        while self.check(&TokenKind::Newline) {
            self.advance();
        }
        // Track if we consumed an indent (need to consume matching dedent)
        let consumed_indent = if self.check(&TokenKind::Indent) {
            self.advance();
            true
        } else {
            false
        };
        let value = self.parse_expression()?;
        // Consume matching dedent if we consumed an indent
        if consumed_indent {
            // Skip newlines before dedent
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }
        Ok((name, ty, value))
    }

    /// Parse optional let-pattern syntax: `let PATTERN =`
    /// Used by if-let and while-let constructs
    pub(crate) fn parse_optional_let_pattern(&mut self) -> Result<(Option<Pattern>, Expr), ParseError> {
        if self.check(&TokenKind::Let) || self.check(&TokenKind::Val) || self.check(&TokenKind::Var) {
            // Emit deprecation warning for `if let` / `while let`
            if self.check(&TokenKind::Let) {
                use crate::error_recovery::{ErrorHint, ErrorHintLevel};
                let warning = ErrorHint {
                    level: ErrorHintLevel::Warning,
                    message: "Deprecated: `if let` syntax".to_string(),
                    span: self.current.span,
                    suggestion: Some("Replace `if let` with `if val` (or `if var` for mutable binding)".to_string()),
                    help: None,
                };
                self.error_hints.push(warning);
            }
            self.advance(); // consume let, val, or var
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::Assign)?;
            let expr = self.parse_expression()?;
            Ok((Some(pattern), expr))
        } else {
            Ok((None, self.parse_expression()?))
        }
    }

    /// Parse implicit val/var: `name = expr` (immutable) or `name_ = expr` (mutable, trailing underscore)
    /// This is syntactic sugar for `val name = expr` / `var name_ = expr`.
    /// Called from parse_item when an identifier is directly followed by `=`.
    pub(crate) fn parse_implicit_val(&mut self) -> Result<Node, ParseError> {
        // TODO: Disabled - implicit val breaks existing `name = expr` reassignments
        return self.parse_expression_or_assignment();
        #[allow(unreachable_code)]
        let start_span = self.current.span;

        // Get identifier name and determine mutability from naming pattern
        let name = match &self.current.kind {
            TokenKind::Identifier { name, .. } => name.clone(),
            _ => unreachable!("parse_implicit_val called without identifier"),
        };

        let mutability = if name.ends_with('_') {
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };

        // Parse pattern (the identifier), optional type annotation, and assignment
        let pattern = self.parse_pattern()?;
        let ty = self.parse_optional_type_annotation()?;
        let (value, is_suspend) = self.parse_optional_assignment_with_suspend()?;

        // Wrap pattern in Pattern::Typed if there's a type annotation
        let pattern = if let Some(type_annotation) = ty {
            Pattern::Typed {
                pattern: Box::new(pattern),
                ty: type_annotation,
            }
        } else {
            pattern
        };

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            ty: None,
            value,
            mutability,
            storage_class: StorageClass::Auto,
            is_ghost: false,
            is_suspend,
        }))
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
            // Emit deprecation warning for '::' syntax
            let warning = ErrorHint {
                level: ErrorHintLevel::Warning,
                message: "Deprecated: '::' in module paths".to_string(),
                span: self.current.span,
                suggestion: Some("Use '.' instead of '::'".to_string()),
                help: Some("Example: use std.spec.* instead of use std::spec::*".to_string()),
            };
            self.error_hints.push(warning);
            self.advance(); // consume ::
        }

        if self.check(&TokenKind::Star) || self.check(&TokenKind::LBrace) {
            let target = self.parse_import_target(None)?;
            Ok((path, target))
        } else if self.check(&TokenKind::LParen) {
            // Python-style parenthesized import: use module (Item1, Item2)
            self.advance(); // consume '('
            let mut targets = Vec::new();
            self.skip_newlines();
            while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
                let name = self.expect_path_segment()?;
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_path_segment()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    if self.check(&TokenKind::Comma) {
                        self.advance();
                        self.skip_newlines();
                    }
                }
            }
            self.expect(&TokenKind::RParen)?;
            Ok((path, ImportTarget::Group(targets)))
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

        // Handle `static fn` at module level (treat as regular function)
        if self.check(&TokenKind::Fn) || self.check(&TokenKind::Me) {
            return self.parse_function_with_decorators(vec![]);
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

    /// Parse unit expression for compound units: length / time, mass * acceleration, time**2
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

    /// Parse a unit term: identifier or identifier**exponent
    fn parse_unit_term(&mut self) -> Result<UnitExpr, ParseError> {
        let name = self.expect_identifier()?;
        let base = UnitExpr::Base(name);

        // Check for power: time**2
        if self.check(&TokenKind::DoubleStar) {
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
                        "Expected integer exponent after '**'",
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
        self.parse_extern_with_attrs(vec![])
    }

    pub(crate) fn parse_extern_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Extern)?;

        // Check if this is `extern class` or `extern fn` or `extern "C":` block
        if self.check(&TokenKind::Class) {
            return self.parse_extern_class_impl(start_span, attributes);
        }

        // Check for extern "C": block syntax (block of FFI declarations)
        if matches!(
            &self.current.kind,
            TokenKind::String(_) | TokenKind::FString(_) | TokenKind::RawString(_)
        ) {
            self.advance(); // consume "C" or other ABI string
            self.expect(&TokenKind::Colon)?;
            // Parse block of extern fn declarations
            self.advance(); // consume newline
            if self.check(&TokenKind::Indent) {
                self.advance();
            }
            let mut nodes = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }
                // Parse each line as extern fn
                self.expect(&TokenKind::Fn)?;
                let name = self.expect_identifier()?;
                let params = self.parse_parameters()?;
                let return_type = if self.check(&TokenKind::Arrow) {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                nodes.push(Node::Extern(ExternDef {
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
                    attributes: attributes.clone(),
                }));
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
            // Return multiple extern declarations wrapped in an expression do-block
            if nodes.len() == 1 {
                return Ok(nodes.into_iter().next().unwrap());
            }
            // Wrap multiple nodes as Expression(DoBlock(nodes))
            return Ok(Node::Expression(Expr::DoBlock(nodes)));
        }

        // Otherwise, parse extern function
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
            attributes,
        }))
    }

    /// Parse extern class definition.
    ///
    /// Syntax:
    /// ```simple
    /// extern class Database:
    ///     static fn open(url: text) -> Result<Database, DbError>
    ///     fn query(sql: text) -> Result<Rows, DbError>
    ///     me execute(sql: text) -> Result<Int, DbError>
    ///     fn close()
    /// ```
    fn parse_extern_class_impl(&mut self, start_span: Span, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        use crate::ast::{DocComment, ExternClassDef, ExternMethodDef, ExternMethodKind};

        self.expect(&TokenKind::Class)?;

        // Parse class name
        let name = self.expect_identifier()?;

        // Parse optional generic parameters: extern class Container<T>
        let generic_params = self.parse_generic_params_as_strings()?;

        // Expect colon and newline for block
        self.expect(&TokenKind::Colon)?;

        // Parse the class body (methods)
        let mut methods = Vec::new();

        // Skip newline
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Expect indent
        if !self.check(&TokenKind::Indent) {
            return Err(ParseError::syntax_error_with_span(
                "Expected indented block after extern class declaration",
                self.current.span,
            ));
        }
        self.advance(); // consume Indent

        // Parse methods until dedent
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Parse optional doc comment for method
            let doc_comment = self.try_parse_doc_comment();

            // Parse optional attributes for method (#[...])
            let method_attrs = if self.check(&TokenKind::Hash) {
                let attr = self.parse_attribute()?;
                vec![attr]
            } else {
                vec![]
            };

            // Determine method kind
            let method_span = self.current.span;
            let kind = if self.check(&TokenKind::Static) {
                self.advance(); // consume 'static'
                self.expect(&TokenKind::Fn)?;
                ExternMethodKind::Static
            } else if self.check(&TokenKind::Me) {
                self.advance(); // consume 'me'
                ExternMethodKind::Mutable
            } else if self.check(&TokenKind::Fn) {
                self.advance(); // consume 'fn'
                ExternMethodKind::Immutable
            } else {
                return Err(ParseError::syntax_error_with_span(
                    "Expected 'static fn', 'fn', or 'me' in extern class method",
                    self.current.span,
                ));
            };

            // Parse method name
            let method_name = self.expect_identifier()?;

            // Parse parameters
            let params = self.parse_parameters()?;

            // Parse optional return type
            let return_type = if self.check(&TokenKind::Arrow) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };

            methods.push(ExternMethodDef {
                span: Span::new(
                    method_span.start,
                    self.previous.span.end,
                    method_span.line,
                    method_span.column,
                ),
                name: method_name,
                kind,
                params,
                return_type,
                attributes: method_attrs,
                doc_comment,
            });

            // Skip newline after method
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume dedent
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::ExternClass(ExternClassDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            methods,
            visibility: Visibility::Private,
            attributes,
            doc_comment: None,
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

#[cfg(test)]
mod tests {
    use crate::Parser;

    #[test]
    fn test_parse_extern_class() {
        let source = r#"extern class Database:
    static fn open(url: text) -> Database
    fn query(sql: text) -> Array
    me execute(sql: text) -> Int
    fn close()
"#;
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("Should parse extern class");

        // Find the extern class
        let extern_class = module
            .items
            .iter()
            .find(|n| matches!(n, crate::ast::Node::ExternClass(_)));
        assert!(extern_class.is_some(), "Should parse extern class");

        if let Some(crate::ast::Node::ExternClass(class)) = extern_class {
            assert_eq!(class.name, "Database");
            assert_eq!(class.methods.len(), 4);

            // Check method kinds
            use crate::ast::ExternMethodKind;
            assert_eq!(class.methods[0].name, "open");
            assert_eq!(class.methods[0].kind, ExternMethodKind::Static);

            assert_eq!(class.methods[1].name, "query");
            assert_eq!(class.methods[1].kind, ExternMethodKind::Immutable);

            assert_eq!(class.methods[2].name, "execute");
            assert_eq!(class.methods[2].kind, ExternMethodKind::Mutable);

            assert_eq!(class.methods[3].name, "close");
            assert_eq!(class.methods[3].kind, ExternMethodKind::Immutable);
        }
    }

    #[test]
    fn test_parse_extern_class_with_generics() {
        let source = r#"extern class Container<T>:
    static fn new() -> Container<T>
    fn get() -> T
    me set(value: T)
"#;
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("Should parse extern class with generics");

        let extern_class = module
            .items
            .iter()
            .find(|n| matches!(n, crate::ast::Node::ExternClass(_)));
        assert!(extern_class.is_some(), "Should parse extern class with generics");

        if let Some(crate::ast::Node::ExternClass(class)) = extern_class {
            assert_eq!(class.name, "Container");
            assert_eq!(class.generic_params, vec!["T".to_string()]);
            assert_eq!(class.methods.len(), 3);
        }
    }

    #[test]
    fn test_parse_extern_fn() {
        // Ensure extern fn still works
        let source = "extern fn rt_print(msg: text)";
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("Should parse extern fn");

        let extern_fn = module.items.iter().find(|n| matches!(n, crate::ast::Node::Extern(_)));
        assert!(extern_fn.is_some(), "Should parse extern fn");

        if let Some(crate::ast::Node::Extern(func)) = extern_fn {
            assert_eq!(func.name, "rt_print");
            assert_eq!(func.params.len(), 1);
        }
    }
}
