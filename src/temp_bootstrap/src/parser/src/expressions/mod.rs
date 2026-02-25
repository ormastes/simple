//! Expression parsing module
//!
//! This module contains all expression parsing logic for the Simple language parser.
//! It implements a Pratt parser (precedence climbing) for binary operators.

use crate::ast::*;
use crate::error::ParseError;
use crate::parser::ParserMode;
use crate::token::{FStringToken, TokenKind};

use super::Parser;

/// Macro to generate binary operator parsing functions.
/// Reduces duplication in precedence-climbing parser.
macro_rules! parse_binary_single {
    ($fn_name:ident, $next_fn:ident, $token:ident, $op:expr) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            let mut total_continuation_depth = 0usize;
            loop {
                // Check for operator on current line
                if self.check(&TokenKind::$token) {
                    // found it
                } else if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                    // Check if operator appears after newline/indent continuation
                    if !self.peek_continuation_for_token(&[TokenKind::$token]) {
                        break;
                    }
                    total_continuation_depth += self.skip_whitespace_for_continuation();
                    if !self.check(&TokenKind::$token) {
                        break;
                    }
                } else {
                    break;
                }
                self.advance();
                // Skip newlines/indent/dedent after binary operator for multi-line expressions
                // Track indent depth so we can consume matching dedents when the loop exits
                total_continuation_depth += self.skip_whitespace_for_continuation();
                let right = self.$next_fn()?;
                left = Expr::Binary {
                    op: $op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
            // Consume matching dedents from all continuation indents
            self.consume_continuation_dedents(total_continuation_depth);
            Ok(left)
        }
    };
}

/// Macro for binary operators with multiple token options
macro_rules! parse_binary_multi {
    ($fn_name:ident, $next_fn:ident, $( $token:ident => $op:expr ),+ $(,)?) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            let mut total_continuation_depth = 0usize;
            loop {
                // Try to match operator on current token
                let op = match &self.current.kind {
                    $( TokenKind::$token => $op, )+
                    // If not found, check for continuation (operator on next line after indent)
                    TokenKind::Newline | TokenKind::Indent => {
                        let target_tokens = vec![$(TokenKind::$token),+];
                        if !self.peek_continuation_for_token(&target_tokens) {
                            break;
                        }
                        total_continuation_depth += self.skip_whitespace_for_continuation();
                        match &self.current.kind {
                            $( TokenKind::$token => $op, )+
                            _ => break,
                        }
                    }
                    _ => break,
                };
                self.advance();
                // Skip newlines/indent/dedent after binary operator for multi-line expressions
                // Track indent depth so we can consume matching dedents when the loop exits
                total_continuation_depth += self.skip_whitespace_for_continuation();
                let right = self.$next_fn()?;
                left = Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
            // Consume matching dedents from all continuation indents
            self.consume_continuation_dedents(total_continuation_depth);
            Ok(left)
        }
    };
}

impl<'a> Parser<'a> {
    /// Helper to convert an expression + args into a Call or MethodCall.
    /// If expr is FieldAccess, create MethodCall; otherwise create Call.
    fn make_call_expr(&self, expr: Expr, args: Vec<Argument>) -> Expr {
        match expr {
            Expr::FieldAccess { receiver, field } => Expr::MethodCall {
                receiver,
                method: field,
                args,
            },
            _ => Expr::Call {
                callee: Box::new(expr),
                args,
            },
        }
    }

    /// Helper to create a Slice expression
    fn make_slice_expr(&self, receiver: Expr, start: Option<Expr>, end: Option<Expr>, step: Option<Box<Expr>>) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }

    // === Expression Parsing (Pratt Parser) ===

    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        let expr = self.parse_null_coalesce()?;

        // Handle postfix `if`: `value if cond else alt_value`
        // Python-style ternary expression.
        // Only match when `if` is on the same line (not a new statement starting with `if`)
        // NOTE: Also exclude cases where previous token was a Dedent/Indent/Newline,
        // because these whitespace tokens can have the same line number as the `if`
        // keyword but actually represent a new statement context.
        let prev_is_whitespace = matches!(
            &self.previous.kind,
            TokenKind::Dedent | TokenKind::Indent | TokenKind::Newline
        );
        if self.check(&TokenKind::If)
            && !prev_is_whitespace
            && self.current.span.line == self.previous.span.line
        {
            self.advance(); // consume 'if'
            let condition = self.parse_null_coalesce()?;
            let else_branch = if self.check(&TokenKind::Else) {
                self.advance(); // consume 'else'
                Some(Box::new(self.parse_null_coalesce()?))
            } else {
                None
            };
            return Ok(Expr::If {
                condition: Box::new(condition),
                then_branch: Box::new(expr),
                else_branch,
            });
        }

        Ok(expr)
    }

    /// Parse null coalescing: expr ?? default (lowest binary precedence)
    fn parse_null_coalesce(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_pipe_forward()?;
        let mut total_continuation_depth = 0usize;
        while self.check(&TokenKind::DoubleQuestion) {
            self.advance();
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let default = self.parse_pipe_forward()?;
            expr = Expr::NullCoalesce {
                expr: Box::new(expr),
                default: Box::new(default),
            };
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(expr)
    }

    /// Parse pipe forward: expr |> func (pipes result into function call)
    fn parse_pipe_forward(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_or()?;
        let mut total_continuation_depth = 0usize;
        while self.check(&TokenKind::PipeForward) {
            self.advance();
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let func = self.parse_or()?;
            // x |> f becomes f(x)
            expr = Expr::Call {
                callee: Box::new(func),
                args: vec![Argument {
                    name: None,
                    value: expr,
                }],
            };
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(expr)
    }

    /// Parse optional step expression for slice syntax (`:step` at end of slice)
    fn parse_optional_step(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::Colon) {
            self.advance();
            if self.check(&TokenKind::RBracket) {
                Ok(None)
            } else {
                Ok(Some(Box::new(self.parse_expression()?)))
            }
        } else {
            Ok(None)
        }
    }

    /// Parse optional expression before RBracket
    fn parse_optional_expr_before_bracket(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::RBracket) {
            Ok(None)
        } else {
            Ok(Some(Box::new(self.parse_expression()?)))
        }
    }

    pub(crate) fn parse_expression_or_assignment(&mut self) -> Result<Node, ParseError> {
        let expr = self.parse_expression()?;

        // Check for walrus operator := (Simple val synonym)
        if self.check(&TokenKind::WalrusAssign) {
            let start_span = self.current.span;
            self.advance();
            let value = self.parse_expression()?;
            // Convert `name := value` to `let name = value` (immutable)
            if let Expr::Identifier(name) = expr {
                return Ok(Node::Let(crate::ast::LetStmt {
                    span: crate::token::Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    pattern: Pattern::Identifier(name),
                    ty: None,
                    value: Some(value),
                    mutability: Mutability::Immutable,
                }));
            }
        }

        // Check for assignment
        let assign_op = match &self.current.kind {
            TokenKind::Assign => Some(AssignOp::Assign),
            TokenKind::PlusAssign => Some(AssignOp::AddAssign),
            TokenKind::MinusAssign => Some(AssignOp::SubAssign),
            TokenKind::StarAssign => Some(AssignOp::MulAssign),
            TokenKind::SlashAssign => Some(AssignOp::DivAssign),
            TokenKind::PercentAssign => Some(AssignOp::ModAssign),
            TokenKind::TildeAssign => Some(AssignOp::TildeAssign),
            _ => None,
        };

        if let Some(op) = assign_op {
            let span = self.current.span;
            self.advance();
            let value = self.parse_expression()?;
            Ok(Node::Assignment(AssignmentStmt {
                span,
                target: expr,
                op,
                value,
            }))
        } else {
            // Parse the expression with potential no-paren calls
            let expr = self.parse_with_no_paren_calls(expr)?;

            // Check for infix keywords (to, not_to) and convert to method calls
            // e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
            let expr = self.parse_infix_keywords(expr)?;

            // Check for trailing colon-block on any call expression:
            // e.g., `describe("test"):` or `it("does thing"):` or `context("when"):`
            // These are function calls followed by `:` + newline + indented block
            let expr = if self.is_at_colon_block() {
                if let Some(block_lambda) = self.try_parse_colon_block()? {
                    // Append the block as a trailing lambda argument to the call
                    match expr {
                        Expr::Call { callee, args } => {
                            let mut new_args = args;
                            new_args.push(Argument {
                                name: None,
                                value: block_lambda,
                            });
                            Expr::Call {
                                callee,
                                args: new_args,
                            }
                        }
                        Expr::MethodCall { receiver, method, args } => {
                            let mut new_args = args;
                            new_args.push(Argument {
                                name: None,
                                value: block_lambda,
                            });
                            Expr::MethodCall {
                                receiver,
                                method,
                                args: new_args,
                            }
                        }
                        other => {
                            // For non-call expressions, wrap as call(block)
                            Expr::Call {
                                callee: Box::new(other),
                                args: vec![Argument {
                                    name: None,
                                    value: block_lambda,
                                }],
                            }
                        }
                    }
                } else {
                    expr
                }
            } else {
                expr
            };

            Ok(Node::Expression(expr))
        }
    }

    /// Parse no-paren calls on an expression
    fn parse_with_no_paren_calls(&mut self, expr: Expr) -> Result<Expr, ParseError> {
        // Check for colon-block on plain identifier FIRST
        // e.g., `given:` or `describe:` without arguments
        // This must come before can_start_argument() check because colon is in that list
        if self.is_callable_expr(&expr) && self.is_at_colon_block() {
            if let Some(block_lambda) = self.try_parse_colon_block()? {
                let args = vec![Argument {
                    name: None,
                    value: block_lambda,
                }];
                return Ok(self.make_call_expr(expr, args));
            }
        }
        // Check for no-parentheses call at statement level
        // Only for identifiers or field access followed by argument-starting tokens
        else if self.is_callable_expr(&expr) && self.can_start_argument() {
            // In strict mode, only allow outermost no-paren call
            // If we're already inside a no-paren call (depth > 0), require parentheses
            if self.mode == ParserMode::Strict && self.no_paren_depth > 0 {
                return Ok(expr);
            }

            // Track depth for strict mode
            self.no_paren_depth += 1;
            let mut args = self.parse_no_paren_arguments()?;
            self.no_paren_depth -= 1;

            // Check for trailing lambda: func arg \x: body
            if self.check(&TokenKind::Backslash) {
                let trailing_lambda = self.parse_trailing_lambda()?;
                args.push(Argument {
                    name: None,
                    value: trailing_lambda,
                });
            }
            // Check for trailing colon-block: func arg:
            //     body
            // This becomes: func(arg, fn(): body)
            else if self.is_at_colon_block() {
                if let Some(block_lambda) = self.try_parse_colon_block()? {
                    args.push(Argument {
                        name: None,
                        value: block_lambda,
                    });
                }
            }

            if !args.is_empty() {
                return Ok(self.make_call_expr(expr, args));
            }
        }
        Ok(expr)
    }

    /// Parse infix keywords (to, not_to) as method calls
    /// e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
    fn parse_infix_keywords(&mut self, mut expr: Expr) -> Result<Expr, ParseError> {
        loop {
            let method_name = match &self.current.kind {
                TokenKind::To => "to",
                TokenKind::NotTo => "not_to",
                _ => break,
            };

            self.advance(); // consume `to` or `not_to`

            // Parse the argument expression (with no-paren calls allowed)
            let arg_expr = self.parse_expression()?;
            let arg_expr = self.parse_with_no_paren_calls(arg_expr)?;

            // Convert to method call: expr.to(arg) or expr.not_to(arg)
            expr = Expr::MethodCall {
                receiver: Box::new(expr),
                method: method_name.to_string(),
                args: vec![Argument {
                    name: None,
                    value: arg_expr,
                }],
            };
        }
        Ok(expr)
    }

    /// Check if an expression can be a callee for no-parens calls
    fn is_callable_expr(&self, expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::Identifier(_) | Expr::FieldAccess { .. } | Expr::Path(_)
        )
    }

    /// Check if we're at a colon-block pattern: `:` followed by newline and indent
    /// This is used to distinguish `func:` blocks from `func name: value` named args
    fn is_at_colon_block(&mut self) -> bool {
        if !self.check(&TokenKind::Colon) {
            return false;
        }

        // Peek ahead to see if there's a newline after the colon
        self.peek_is(&TokenKind::Newline)
    }

    /// Check if current token can start an argument (for no-parens calls)
    fn can_start_argument(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Integer(_)
                | TokenKind::TypedInteger(_, _)
                | TokenKind::Float(_)
                | TokenKind::TypedFloat(_, _)
                | TokenKind::String(_)
                | TokenKind::RawString(_)
                | TokenKind::TypedString(_, _)
                | TokenKind::TypedRawString(_, _)
                | TokenKind::FString(_)
                | TokenKind::Bool(_)
                | TokenKind::Nil
                | TokenKind::Symbol(_)
                | TokenKind::Identifier(_)
                | TokenKind::Result     // 'result' can be used as variable name
                | TokenKind::Type       // 'type' can be used as variable name
                | TokenKind::Out        // 'out' can be used as variable name
                | TokenKind::OutErr     // 'out_err' can be used as variable name
                | TokenKind::Self_     // self.method() as argument
                | TokenKind::Super     // super.method() as argument
                | TokenKind::New       // new Foo() as argument
                | TokenKind::Spawn     // spawn foo() as argument
                | TokenKind::From      // 'from' can be used as variable name
                | TokenKind::To        // 'to' can be used as variable name
                | TokenKind::NotTo     // 'not_to' can be used as variable name
                | TokenKind::Context   // 'context' can be used as variable name
                | TokenKind::Old       // 'old' can be used as variable name
                | TokenKind::Match     // 'match' can be used as variable name
                | TokenKind::In        // 'in' can be used as variable name
                | TokenKind::As        // 'as' can be used as variable name
                | TokenKind::Is        // 'is' can be used as variable name
                | TokenKind::Static   // 'static' can be used as variable/function name
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
                | TokenKind::Backslash
                | TokenKind::Colon // for named args like name: "value"
                // Unary prefix operators that can start expressions
                | TokenKind::Await    // await expr
                | TokenKind::Yield    // yield expr
                | TokenKind::Not      // not expr
                | TokenKind::Minus    // -expr (negation)
                | TokenKind::Plus     // +expr
                | TokenKind::Tilde    // ~expr (bitwise not)
                | TokenKind::Ampersand // &expr (reference)
                | TokenKind::Star     // *expr (dereference)
        )
    }

    /// Parse arguments without parentheses.
    /// - Normal mode: comma-separated (required)
    /// - Strict mode: commas optional, space-separated allowed
    fn parse_no_paren_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        let mut args = Vec::new();

        // Parse first argument
        if let Ok(arg) = self.parse_single_argument() {
            args.push(arg);
        } else {
            return Ok(args);
        }

        // Parse remaining arguments
        loop {
            // Check for comma (required in normal mode, optional in strict mode)
            let has_comma = self.check(&TokenKind::Comma);
            if has_comma {
                self.advance(); // consume comma
            }

            // In strict mode, continue parsing if we can start another argument
            // In normal mode, require comma to continue
            if self.mode == ParserMode::Strict {
                // Strict mode: commas optional, continue if can start argument
                if !self.can_start_argument() {
                    break;
                }
            } else {
                // Normal mode: require comma to continue
                if !has_comma {
                    break;
                }
            }

            // Parse next argument
            if let Ok(arg) = self.parse_single_argument() {
                args.push(arg);
            } else {
                break;
            }
        }

        Ok(args)
    }

    /// Parse a single argument (possibly named)
    fn parse_single_argument(&mut self) -> Result<Argument, ParseError> {
        // Check for named argument: name: value
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name_clone = name.clone();
            // Peek ahead to check for colon
            if self.peek_is(&TokenKind::Colon) {
                self.advance(); // consume identifier
                self.advance(); // consume colon
                // In strict mode, track depth when parsing named argument value
                let prev_depth = self.no_paren_depth;
                if self.mode == ParserMode::Strict {
                    self.no_paren_depth += 1;
                }
                let value = self.parse_expression()?;
                self.no_paren_depth = prev_depth;
                return Ok(Argument {
                    name: Some(name_clone),
                    value,
                });
            }
        }
        // Positional argument
        // In strict mode, track depth when parsing argument value
        let prev_depth = self.no_paren_depth;
        if self.mode == ParserMode::Strict {
            self.no_paren_depth += 1;
        }
        let value = self.parse_expression()?;
        self.no_paren_depth = prev_depth;
        Ok(Argument { name: None, value })
    }

    // Binary expression parsing with precedence (using macros to reduce duplication)
    // Precedence (lowest to highest): or, and, equality, comparison, bitwise_or, bitwise_xor, bitwise_and, shift, term, factor, power

    // Single-token operators
    // Hand-written parse_or and parse_and to handle multi-line conditions:
    //   if cond1 and cond2
    //      and cond3:
    pub(crate) fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;
        let mut total_continuation_depth = 0usize;
        while self.check(&TokenKind::Or) || self.peek_past_newline_for(&TokenKind::Or) {
            if self.check(&TokenKind::Newline) {
                self.advance(); // consume Newline
                total_continuation_depth += self.skip_whitespace_for_continuation();
            }
            self.advance(); // consume 'or'
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let right = self.parse_and()?;
            left = Expr::Binary {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(left)
    }
    pub(crate) fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_equality()?;
        let mut total_continuation_depth = 0usize;
        while self.check(&TokenKind::And) || self.peek_past_newline_for(&TokenKind::And) {
            if self.check(&TokenKind::Newline) {
                self.advance(); // consume Newline
                total_continuation_depth += self.skip_whitespace_for_continuation();
            }
            self.advance(); // consume 'and'
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let right = self.parse_equality()?;
            left = Expr::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(left)
    }
    parse_binary_single!(parse_bitwise_or, parse_bitwise_xor, Pipe, BinOp::BitOr);
    // Hand-written to handle both ^ and keyword 'xor'
    pub(crate) fn parse_bitwise_xor(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_bitwise_and()?;
        let mut total_continuation_depth = 0usize;
        loop {
            if self.check(&TokenKind::Caret) {
                self.advance();
                total_continuation_depth += self.skip_whitespace_for_continuation();
                let right = self.parse_bitwise_and()?;
                left = Expr::Binary {
                    op: BinOp::BitXor,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "xor") {
                self.advance();
                total_continuation_depth += self.skip_whitespace_for_continuation();
                let right = self.parse_bitwise_and()?;
                left = Expr::Binary {
                    op: BinOp::BitXor,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(left)
    }
    parse_binary_single!(parse_bitwise_and, parse_shift, Ampersand, BinOp::BitAnd);

    // Equality and membership operators (including multi-token "not in")
    pub(crate) fn parse_equality(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;
        let mut total_continuation_depth = 0usize;
        loop {
            let op = match &self.current.kind {
                TokenKind::Eq => BinOp::Eq,
                TokenKind::NotEq => BinOp::NotEq,
                TokenKind::Is => BinOp::Is,
                TokenKind::In => BinOp::In,
                TokenKind::Not => {
                    // Check for "not in" two-token operator
                    if self.peek_is(&TokenKind::In) {
                        self.advance(); // consume 'not'
                        BinOp::NotIn
                    } else {
                        break;
                    }
                }
                _ => break,
            };
            self.advance();
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let right = self.parse_comparison()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        self.consume_continuation_dedents(total_continuation_depth);
        Ok(left)
    }

    /// Parse range expressions: a..b (exclusive) or a..=b (inclusive)
    pub(crate) fn parse_range(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_bitwise_or()?;

        if self.check(&TokenKind::DoubleDot) {
            self.advance();
            // Open-ended range: expr.. (e.g. arr[1..])
            let end = if self.check(&TokenKind::RBracket)
                || self.check(&TokenKind::RParen)
                || self.check(&TokenKind::Comma)
                || self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Colon)
                || self.check(&TokenKind::Semicolon)
            {
                None
            } else {
                Some(Box::new(self.parse_bitwise_or()?))
            };
            return Ok(Expr::Range {
                start: Some(Box::new(left)),
                end,
                bound: RangeBound::Exclusive,
            });
        }

        if self.check(&TokenKind::DoubleDotEq) {
            self.advance();
            let right = self.parse_bitwise_or()?;
            return Ok(Expr::Range {
                start: Some(Box::new(left)),
                end: Some(Box::new(right)),
                bound: RangeBound::Inclusive,
            });
        }

        Ok(left)
    }

    /// Parse comparisons with chaining support: a < b < c becomes (a < b) and (b < c)
    pub(crate) fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_range()?;

        // Check if there's a comparison operator
        let op = match &self.current.kind {
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::LtEq => Some(BinOp::LtEq),
            TokenKind::GtEq => Some(BinOp::GtEq),
            _ => None,
        };

        if op.is_none() {
            return Ok(left);
        }

        // We have at least one comparison
        let mut comparisons: Vec<Expr> = Vec::new();
        let mut prev_right = left;
        let mut total_continuation_depth = 0usize;

        loop {
            let op = match &self.current.kind {
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::LtEq => BinOp::LtEq,
                TokenKind::GtEq => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            // Skip newlines/indent/dedent after comparison operator
            total_continuation_depth += self.skip_whitespace_for_continuation();
            let right = self.parse_range()?;

            comparisons.push(Expr::Binary {
                op,
                left: Box::new(prev_right.clone()),
                right: Box::new(right.clone()),
            });

            prev_right = right;
        }
        self.consume_continuation_dedents(total_continuation_depth);

        // If only one comparison, return it directly
        if comparisons.len() == 1 {
            return Ok(comparisons.into_iter().next().unwrap());
        }

        // Chain multiple comparisons with 'and'
        let mut result = comparisons.remove(0);
        for cmp in comparisons {
            result = Expr::Binary {
                op: BinOp::And,
                left: Box::new(result),
                right: Box::new(cmp),
            };
        }

        Ok(result)
    }

    parse_binary_multi!(parse_shift, parse_term,
        ShiftLeft => BinOp::ShiftLeft,
        ShiftRight => BinOp::ShiftRight,
    );

    parse_binary_multi!(parse_term, parse_factor,
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
    );

    parse_binary_multi!(parse_factor, parse_power,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Mod,
        DoubleSlash => BinOp::FloorDiv,
        At => BinOp::MatMul,
    );

    pub(crate) fn parse_power(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_unary()?;

        if self.check(&TokenKind::DoubleStar) {
            self.advance();
            let right = self.parse_power()?; // Right associative
            return Ok(Expr::Binary {
                op: BinOp::Pow,
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    pub(crate) fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Plus => {
                // Unary plus: +expr (identity, but valid syntax)
                self.advance();
                self.parse_unary()
            }
            TokenKind::Minus => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Not => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Bang => {
                // `!expr` as prefix NOT operator (C/Rust style)
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Tilde => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::BitNot,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Ampersand => {
                self.advance();
                // Check for &mut expr (mutable borrow)
                if self.check(&TokenKind::Mut) {
                    self.advance();
                    let operand = self.parse_unary()?;
                    Ok(Expr::Unary {
                        op: UnaryOp::RefMut,
                        operand: Box::new(operand),
                    })
                } else {
                    let operand = self.parse_unary()?;
                    Ok(Expr::Unary {
                        op: UnaryOp::Ref,
                        operand: Box::new(operand),
                    })
                }
            }
            TokenKind::Star => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Deref,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Await => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Await(Box::new(operand)))
            }
            TokenKind::Yield => {
                self.advance();
                // yield can be bare (yield) or with value (yield expr)
                if self.is_at_end()
                    || matches!(
                        self.current.kind,
                        TokenKind::Newline
                            | TokenKind::Dedent
                            | TokenKind::RParen
                            | TokenKind::RBrace
                            | TokenKind::Comma
                    )
                {
                    Ok(Expr::Yield(None))
                } else {
                    let operand = self.parse_unary()?;
                    Ok(Expr::Yield(Some(Box::new(operand))))
                }
            }
            _ => self.parse_postfix(),
        }
    }

    pub(crate) fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            match &self.current.kind {
                // Handle generic type instantiation: Dict<i64, Foo>.new()
                // When we see Identifier followed by <, check if it looks like generic type args
                TokenKind::Lt if matches!(&expr, Expr::Identifier(name) if name.chars().next().map_or(false, |c| c.is_uppercase())) => {
                    // Try to parse as generic type args: save state for backtracking
                    // Heuristic: if we see Identifier< followed by type names/commas and >,
                    // treat as generic type instantiation
                    if self.try_parse_generic_type_suffix(&mut expr) {
                        // Successfully parsed generic type suffix, continue loop
                        continue;
                    } else {
                        // Not a generic type, break to let comparison handle it
                        break;
                    }
                }
                TokenKind::LParen => {
                    expr = self.parse_call(expr)?;
                }
                TokenKind::Bang => {
                    // Macro invocation: name!(args)
                    if let Expr::Identifier(name) = expr {
                        self.advance(); // consume !
                        let args = self.parse_macro_args()?;
                        expr = Expr::MacroInvocation { name, args };
                    } else {
                        break;
                    }
                }
                TokenKind::LBracket => {
                    self.advance();

                    // Check for slicing: arr[start:end:step] or arr[:] or arr[::step]
                    // Note: :: is lexed as DoubleColon, so we need to handle both Colon and DoubleColon
                    if self.check(&TokenKind::DoubleColon) {
                        // Slice starting with :: (no start, no end)
                        self.advance();
                        let step = self.parse_optional_expr_before_bracket()?;
                        self.expect(&TokenKind::RBracket)?;
                        expr = self.make_slice_expr(expr, None, None, step);
                    } else if self.check(&TokenKind::Colon) {
                        // Slice starting with : (no start)
                        self.advance();
                        // Check for ::step (no end)
                        if self.check(&TokenKind::Colon) {
                            self.advance();
                            let step = self.parse_optional_expr_before_bracket()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = self.make_slice_expr(expr, None, None, step);
                        } else {
                            let end = self.parse_optional_expr_before_bracket()?;
                            let step = self.parse_optional_step()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: None,
                                end,
                                step,
                            };
                        }
                    } else {
                        // Parse first expression (could be index or slice start)
                        let first = self.parse_expression()?;

                        if self.check(&TokenKind::DoubleColon) {
                            // Slice with start::step (no end)
                            self.advance();
                            let step = self.parse_optional_expr_before_bracket()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: Some(Box::new(first)),
                                end: None,
                                step,
                            };
                        } else if self.check(&TokenKind::Colon) {
                            // It's a slice
                            self.advance();
                            let end = if self.check(&TokenKind::Colon)
                                || self.check(&TokenKind::RBracket)
                            {
                                None
                            } else {
                                Some(Box::new(self.parse_expression()?))
                            };
                            let step = self.parse_optional_step()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: Some(Box::new(first)),
                                end,
                                step,
                            };
                        } else {
                            // Regular index access
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Index {
                                receiver: Box::new(expr),
                                index: Box::new(first),
                            };
                        }
                    }
                }
                TokenKind::Dot => {
                    self.advance();
                    // Optional check operator: expr.? — returns true if optional has value
                    if self.check(&TokenKind::Question) {
                        self.advance();
                        expr = Expr::OptionalCheck(Box::new(expr));
                    } else if let TokenKind::Integer(n) = &self.current.kind {
                        // Support tuple element access: tuple.0, tuple.1
                        let index = *n;
                        self.advance();
                        expr = Expr::TupleIndex {
                            receiver: Box::new(expr),
                            index: index as usize,
                        };
                    } else if self.check(&TokenKind::LParen) {
                        // Computed property access: obj.(expr)
                        // Parses as Index with the computed expression
                        self.advance(); // consume '('
                        let index_expr = self.parse_expression()?;
                        self.expect(&TokenKind::RParen)?;
                        expr = Expr::Index {
                            receiver: Box::new(expr),
                            index: Box::new(index_expr),
                        };
                    } else {
                        let field = self.expect_method_name()?;
                        if self.check(&TokenKind::LParen) {
                            let mut args = self.parse_arguments()?;
                            // Check for trailing block: obj.method(args) \x: body
                            if self.check(&TokenKind::Backslash) {
                                let trailing_lambda = self.parse_trailing_lambda()?;
                                args.push(Argument {
                                    name: None,
                                    value: trailing_lambda,
                                });
                            }
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args,
                            };
                        } else if self.check(&TokenKind::Backslash) {
                            // Method call with only trailing block: obj.method \x: body
                            let trailing_lambda = self.parse_trailing_lambda()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument {
                                    name: None,
                                    value: trailing_lambda,
                                }],
                            };
                        } else {
                            expr = Expr::FieldAccess {
                                receiver: Box::new(expr),
                                field,
                            };
                        }
                    }
                }
                TokenKind::DoubleColon => {
                    // Static/associated access: Type::method() or Type::CONST
                    // Treated like dot access for method/field
                    self.advance();
                    let field = self.expect_method_name()?;
                    if self.check(&TokenKind::LParen) {
                        let args = self.parse_arguments()?;
                        expr = Expr::MethodCall {
                            receiver: Box::new(expr),
                            method: field,
                            args,
                        };
                    } else {
                        expr = Expr::FieldAccess {
                            receiver: Box::new(expr),
                            field,
                        };
                    }
                }
                TokenKind::Arrow => {
                    // Functional update operator: obj->method(args)
                    // Desugars to: obj = obj.method(args)
                    self.advance();
                    let method = self.expect_method_name()?;
                    let args = self.parse_arguments()?;
                    expr = Expr::FunctionalUpdate {
                        target: Box::new(expr),
                        method,
                        args,
                    };
                }
                TokenKind::Question => {
                    // Try operator: expr? - unwrap Ok or early return Err
                    self.advance();
                    expr = Expr::Try(Box::new(expr));
                }
                TokenKind::As => {
                    // Type cast: expr as Type
                    // Use parse_type_for_cast to avoid consuming ?? as optional suffix
                    // (in `expr as i64 ?? default`, ?? is null-coalesce, not double-optional)
                    self.advance();
                    let target_type = self.parse_type_for_cast()?;
                    expr = Expr::TypeCast {
                        expr: Box::new(expr),
                        target_type,
                    };
                }
                TokenKind::Newline => {
                    // Check if this is method chaining across lines.
                    // Peek past newline (and optional Indent) to see if the next
                    // meaningful token is '.' which would indicate continued method chaining.
                    if self.peek_past_newline_for(&TokenKind::Dot) {
                        // Skip newline and Indent tokens, then continue chaining.
                        // When we consume Indent tokens for continuation, pop the
                        // indent_stack entry so the lexer doesn't generate spurious
                        // Dedent tokens later.
                        self.advance(); // consume Newline
                        while self.check(&TokenKind::Indent) || self.check(&TokenKind::Newline) {
                            if self.check(&TokenKind::Indent) {
                                self.advance();
                                self.lexer.indent_stack.pop();
                            } else {
                                self.advance();
                            }
                        }
                    } else {
                        break;
                    }
                }
                // Handle @volatile val: Type / @volatile var: Type — volatile memory access annotation
                // Pattern: @address(expr) @volatile val: Type
                TokenKind::At => {
                    // Peek ahead: if next is "volatile" and then val/var/let, consume it
                    let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                    self.pending_token = Some(next.clone());
                    if matches!(&next.kind, TokenKind::Identifier(s) if s == "volatile") {
                        self.advance(); // consume @
                        self.advance(); // consume "volatile"
                        // Expect val/var/let
                        if self.check(&TokenKind::Let) || self.check(&TokenKind::Var) {
                            self.advance(); // consume val/var
                        }
                        // Expect : Type
                        if self.check(&TokenKind::Colon) {
                            self.advance(); // consume :
                            let _ty = self.parse_type()?;
                        }
                        // The expression remains the @address(...) call, just with volatile annotation consumed
                    } else {
                        break;
                    }
                }
                // Handle unit suffix: expr_bytes, expr_ms, expr_kb, etc.
                // An identifier starting with '_' immediately following an expression is a unit suffix.
                // ONLY when the previous token was NOT a structural whitespace token (Dedent, Newline, Indent)
                // — a _-prefixed identifier after a block boundary is a new statement, not a unit suffix.
                TokenKind::Identifier(id) if id.starts_with('_')
                    && !matches!(self.previous.kind, TokenKind::Dedent | TokenKind::Newline | TokenKind::Indent) => {
                    let suffix = id.clone();
                    self.advance();
                    // Represent as a field access with the suffix name (e.g., expr._bytes)
                    // Semantics are resolved later by the type system
                    expr = Expr::FieldAccess {
                        receiver: Box::new(expr),
                        field: suffix,
                    };
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    pub(crate) fn parse_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mut args = self.parse_arguments()?;
        // Check for trailing block: func(args) \x: body
        if self.check(&TokenKind::Backslash) {
            let trailing_lambda = self.parse_trailing_lambda()?;
            args.push(Argument {
                name: None,
                value: trailing_lambda,
            });
        }
        // Note: Colon-block syntax like func(args): body is only supported in the
        // no-paren call context (parse_expression_or_assignment), not here.
        // This avoids conflicts with for/while/if statements that use colon after expressions.
        Ok(Expr::Call {
            callee: Box::new(callee),
            args,
        })
    }

    /// Parse a trailing block lambda: \params: body
    pub(crate) fn parse_trailing_lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::Backslash)?;
        let params = self.parse_lambda_params()?;
        self.expect(&TokenKind::Colon)?;

        // For lambda bodies inside brackets, temporarily disable bracket depth
        // so the lexer emits INDENT/DEDENT tokens for nested blocks (for, if, etc.)
        let body = if self.check(&TokenKind::Newline) {
            if self.lexer.bracket_depth > 0 {
                // Multi-line lambda body inside brackets (INDENT suppressed).
                // Temporarily set bracket_depth to 0 BEFORE consuming the Newline
                // so the lexer processes indentation on the next line.
                let saved_depth = self.lexer.bracket_depth;
                self.lexer.bracket_depth = 0;
                // Now consume Newline — lexer will set at_line_start = true
                self.advance();
                // The next token should be INDENT (since bracket_depth is 0)
                if self.check(&TokenKind::Indent) {
                    let block = self.parse_block()?;
                    // Consume any leftover DEDENTs
                    while self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                    self.lexer.bracket_depth = saved_depth;
                    Expr::DoBlock(block.statements)
                } else {
                    // No INDENT was emitted — restore bracket_depth and fall back
                    self.lexer.bracket_depth = saved_depth;
                    // Skip leading newlines
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    let mut stmts = Vec::new();
                    loop {
                        if self.is_at_end() {
                            break;
                        }
                        match &self.current.kind {
                            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
                                if self.lexer.bracket_depth <= saved_depth =>
                            {
                                break;
                            }
                            TokenKind::Comma if self.lexer.bracket_depth <= saved_depth => {
                                break;
                            }
                            TokenKind::Dedent => {
                                self.advance();
                                continue;
                            }
                            _ => {}
                        }
                        let item = self.parse_item()?;
                        stmts.push(item);
                        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Semicolon) {
                            self.advance();
                        }
                    }
                    if stmts.len() == 1 {
                        if let Some(crate::ast::Node::Expression(expr)) = stmts.into_iter().next() {
                            expr
                        } else {
                            Expr::Nil
                        }
                    } else {
                        Expr::DoBlock(stmts)
                    }
                }
            } else if self.peek_is(&TokenKind::Indent) {
                let block = self.parse_block()?;
                Expr::DoBlock(block.statements)
            } else {
                // bracket_depth == 0 but no INDENT peek — single newline before expression
                self.advance(); // consume newline
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                self.parse_expression()?
            }
        } else if self.check(&TokenKind::LBrace) {
            // Brace-delimited block: \: { stmt1; stmt2; expr }
            self.advance(); // consume '{'
            self.skip_whitespace_tokens();
            let mut stmts = Vec::new();
            while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                self.skip_whitespace_tokens();
                if self.check(&TokenKind::RBrace) { break; }
                let item = self.parse_item()?;
                stmts.push(item);
                while self.check(&TokenKind::Semicolon) || self.check(&TokenKind::Newline) {
                    self.advance();
                }
            }
            self.expect(&TokenKind::RBrace)?;
            Expr::DoBlock(stmts)
        } else {
            // Inline expression (same line)
            self.parse_expression()?
        };

        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode: MoveMode::Copy,
        })
    }

    /// Parse lambda parameters (comma-separated identifiers before colon)
    /// Used by both trailing lambda and inline lambda parsing
    pub(crate) fn parse_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
        let mut params = Vec::new();
        // Check for no-param lambda: \: expr
        if !self.check(&TokenKind::Colon) {
            self.parse_one_lambda_param(&mut params)?;
            self.parse_remaining_lambda_params(&mut params)?;
        }
        Ok(params)
    }

    /// Parse a single lambda parameter — either an identifier or a destructured tuple (a, b)
    fn parse_one_lambda_param(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        if self.check(&TokenKind::LParen) {
            // Destructured tuple parameter: \(a, b): body
            self.advance(); // consume '('
            let mut names = Vec::new();
            while !self.check(&TokenKind::RParen) && !self.is_at_end() {
                if self.check(&TokenKind::Underscore) {
                    self.advance();
                    names.push("_".to_string());
                } else {
                    names.push(self.expect_identifier()?);
                }
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            // Represent as synthetic name for each destructured element
            for name in names {
                params.push(LambdaParam { name, ty: None });
            }
            Ok(())
        } else if self.check(&TokenKind::Underscore) {
            self.advance();
            params.push(LambdaParam { name: "_".to_string(), ty: None });
            Ok(())
        } else {
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
            Ok(())
        }
    }

    /// Parse lambda parameters between pipes: |x| or |x, y|
    /// Called after the opening pipe has been consumed.
    pub(crate) fn parse_pipe_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
        let mut params = Vec::new();
        // Check for no-param lambda: || expr
        if !self.check(&TokenKind::Pipe) {
            self.parse_one_pipe_param(&mut params)?;
            // Parse remaining params separated by commas
            while self.check(&TokenKind::Comma) {
                self.advance();
                self.parse_one_pipe_param(&mut params)?;
            }
        }
        Ok(params)
    }

    /// Parse a single pipe lambda parameter: identifier, underscore, &ref, or destructured tuple
    fn parse_one_pipe_param(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        // Handle reference patterns: |&b| expr or |&mut b| expr
        if self.check(&TokenKind::Ampersand) {
            self.advance(); // consume '&'
            if self.check(&TokenKind::Mut) {
                self.advance(); // consume 'mut'
            }
            if self.check(&TokenKind::Underscore) {
                self.advance();
                params.push(LambdaParam { name: "_".to_string(), ty: None });
            } else {
                let name = self.expect_identifier()?;
                params.push(LambdaParam { name, ty: None });
            }
            return Ok(());
        }
        if self.check(&TokenKind::Underscore) {
            self.advance();
            params.push(LambdaParam { name: "_".to_string(), ty: None });
            Ok(())
        } else if self.check(&TokenKind::LParen) {
            // Destructured tuple: (a, b) or (a, _)
            self.advance(); // consume '('
            let mut names = Vec::new();
            while !self.check(&TokenKind::RParen) && !self.is_at_end() {
                if self.check(&TokenKind::Underscore) {
                    self.advance();
                    names.push("_".to_string());
                } else {
                    names.push(self.expect_identifier()?);
                }
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            for name in names {
                params.push(LambdaParam { name, ty: None });
            }
            Ok(())
        } else {
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
            Ok(())
        }
    }

    /// Helper to parse remaining comma-separated lambda parameters
    fn parse_remaining_lambda_params(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        while self.check(&TokenKind::Comma) {
            self.advance();
            self.parse_one_lambda_param(params)?;
        }
        Ok(())
    }

    /// Try to parse a colon-block as a trailing lambda.
    ///
    /// Syntax:
    /// ```text
    /// func arg:
    ///     statement1
    ///     statement2
    /// ```
    ///
    /// This is parsed as `func(arg, fn(): statement1; statement2)`.
    ///
    /// Returns `Some(lambda)` if we see `:` followed by newline and indent,
    /// `None` if this doesn't look like a colon-block.
    fn try_parse_colon_block(&mut self) -> Result<Option<Expr>, ParseError> {
        // Must be at a colon
        if !self.check(&TokenKind::Colon) {
            return Ok(None);
        }

        // Peek ahead to see if this is a colon-block
        // We need: colon, newline, indent
        // Since we can't easily peek multiple tokens, we'll consume and check
        self.advance(); // consume ':'

        // Skip any newlines after the colon
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Must have indent for a block
        if !self.check(&TokenKind::Indent) {
            // No indent after colon-newline - this is an empty block (e.g., block with only comments).
            // Treat as an empty trailing lambda (pass_do_nothing equivalent).
            return Ok(Some(Expr::Lambda {
                params: vec![],
                body: Box::new(Expr::DoBlock(vec![Node::Expression(Expr::Nil)])),
                move_mode: MoveMode::Copy,
            }));
        }

        self.advance(); // consume Indent

        // Parse statements until dedent
        let mut statements = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
            // Skip newlines between statements
            while self.check(&TokenKind::Newline) {
                self.advance();
            }

            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                break;
            }

            let stmt = self.parse_item()?;
            statements.push(stmt);

            // Skip trailing newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume dedent if present
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        // Wrap statements in a DoBlock expression, then in a Lambda
        let block_expr = Expr::DoBlock(statements);

        Ok(Some(Expr::Lambda {
            params: vec![],
            body: Box::new(block_expr),
            move_mode: MoveMode::Copy,
        }))
    }

    /// Parse an if/elif expression (shared logic)
    /// Supports both inline: `if cond: expr else: expr`
    /// and block form: `if cond:\n    expr\n else:\n    expr`
    pub(crate) fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        // Handle 'if val pattern = expr:' (pattern binding in condition)
        let let_pattern = if self.check(&TokenKind::Let) {
            self.advance();
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::Assign)?;
            Some(pattern)
        } else {
            None
        };
        let condition = self.parse_expression()?;
        let condition = if let Some(pattern) = let_pattern {
            // Wrap as LetPattern expression
            Expr::LetBinding {
                pattern,
                value: Box::new(condition),
            }
        } else {
            condition
        };
        // Accept ':', 'then', or '{' as delimiters
        let is_brace_delimited = if self.check(&TokenKind::Colon) {
            self.advance();
            false
        } else if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "then") {
            self.advance();
            false
        } else if self.check(&TokenKind::LBrace) {
            // C-style brace-delimited if: if cond { body } else { body }
            true
        } else {
            self.expect(&TokenKind::Colon)?;
            false
        };

        // Parse then branch: inline, block, or brace-delimited
        let then_branch = if is_brace_delimited {
            self.parse_brace_block_expr()?
        } else {
            self.parse_expr_or_block_expr()?
        };

        // Skip newlines (and Indent tokens) before elif/else (for block-form if expressions)
        // When else/elif is on a continuation line with deeper indentation, the token
        // sequence is: Newline -> Indent -> Else/Elif. We need to peek past both.
        if self.check(&TokenKind::Newline) {
            // Save parser state in case we need to restore
            let saved_current = self.current.clone();
            let saved_previous = self.previous.clone();
            let saved_pending = self.pending_token.clone();
            let saved_indent_stack_len = self.lexer.indent_stack.len();

            self.advance(); // consume Newline

            // Collect tokens we consumed so we can push them back if needed
            let mut consumed_tokens: Vec<crate::token::Token> = Vec::new();
            let first_from_pending = saved_pending.is_some();
            if !first_from_pending {
                consumed_tokens.push(self.current.clone());
            }

            // Skip Indent/Dedent/Newline tokens to find elif/else
            // Track Indent tokens so we can pop indent_stack if we keep them
            let mut indent_count = 0usize;
            while self.check(&TokenKind::Indent) || self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                if self.check(&TokenKind::Indent) {
                    indent_count += 1;
                }
                self.advance();
                consumed_tokens.push(self.current.clone());
            }

            if self.check(&TokenKind::Elif) || self.check(&TokenKind::Else) {
                // Found elif/else - keep consuming (don't restore).
                // Pop indent_stack entries for consumed Indent tokens to prevent
                // spurious Dedent generation later. The Indent tokens here are just
                // continuation indentation, not block structure.
                for _ in 0..indent_count {
                    self.lexer.indent_stack.pop();
                }
            } else {
                // Not elif/else - restore parser state completely
                let leftover_pending = self.pending_token.take();
                if let Some(lp) = leftover_pending {
                    self.lexer.pending_tokens.push(lp);
                }
                for tok in consumed_tokens.into_iter().rev() {
                    self.lexer.pending_tokens.push(tok);
                }
                self.current = saved_current;
                self.previous = saved_previous;
                self.pending_token = saved_pending;
                // Restore indent_stack to saved state
                while self.lexer.indent_stack.len() > saved_indent_stack_len {
                    self.lexer.indent_stack.pop();
                }
            }
        }

        let else_branch = if self.check(&TokenKind::Elif) {
            self.advance();
            Some(Box::new(self.parse_if_expr()?))
        } else if self.check(&TokenKind::Else) {
            self.advance();
            // Handle `else if` as `elif` (else followed by if without colon)
            if self.check(&TokenKind::If) {
                self.advance();
                Some(Box::new(self.parse_if_expr()?))
            } else if self.check(&TokenKind::LBrace) {
                // C-style brace-delimited else: else { body }
                Some(Box::new(self.parse_brace_block_expr()?))
            } else {
                // Accept both `else:` and `else expr` (colon-less inline else)
                if self.check(&TokenKind::Colon) {
                    self.advance();
                }
                Some(Box::new(self.parse_expr_or_block_expr()?))
            }
        } else {
            None
        };
        Ok(Expr::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch,
        })
    }

    /// Parse an expression that might be on the next line (block form).
    /// If current token is Newline, parse the indented block and extract
    /// the last expression as the block's value.
    fn parse_expr_or_block_expr(&mut self) -> Result<Expr, ParseError> {
        if self.check(&TokenKind::Newline) {
            // Block form
            let block = self.parse_block_or_inline()?;
            // Extract the last expression from the block
            if let Some(last) = block.statements.last() {
                match last {
                    crate::ast::Node::Expression(expr) => Ok(expr.clone()),
                    _ => {
                        // Wrap the block into a DoBlock expression
                        Ok(Expr::DoBlock(block.statements.clone()))
                    }
                }
            } else {
                Ok(Expr::Nil)
            }
        } else if self.check(&TokenKind::Return)
            || self.check(&TokenKind::Break)
            || self.check(&TokenKind::Continue)
        {
            // Statement keyword in expression context (e.g., `if cond: return nil`)
            // Parse as a statement and wrap in DoBlock
            let stmt = self.parse_item()?;
            Ok(Expr::DoBlock(vec![stmt]))
        } else {
            self.parse_expression()
        }
    }

    /// Parse a brace-delimited block expression: `{ expr }` or `{ statements... }`
    /// Used for C-style if/else: `if cond { body } else { body }`
    fn parse_brace_block_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::LBrace)?;
        self.skip_whitespace_tokens();
        // Parse expression(s) until RBrace
        if self.check(&TokenKind::RBrace) {
            self.advance();
            return Ok(Expr::Nil);
        }
        let expr = self.parse_expression()?;
        self.skip_whitespace_tokens();
        // Skip newlines/dedent before closing brace
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
            self.advance();
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(expr)
    }

    pub(crate) fn parse_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();

        // Skip newlines and indent after opening paren (for multi-line argument lists)
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            self.advance();
        }

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            // Skip any stray whitespace tokens at the start of each argument
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
            {
                self.advance();
            }
            if self.check(&TokenKind::RParen) {
                break;
            }

            // Handle inline val/var bindings inside constructor args:
            // e.g., `Foo(x: 1, val _tmp = (0, 0), y: _tmp)`
            // Parse and skip the binding, then continue to the next argument.
            // Must peek ahead to distinguish `val name = expr` from `val` used as a variable name.
            if (self.check(&TokenKind::Let) && {
                // Peek ahead: val followed by identifier is a binding
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                matches!(next.kind, TokenKind::Identifier(_))
            }) || (self.check(&TokenKind::Var) && {
                // Peek ahead: var followed by identifier then '=' is a binding
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                matches!(next.kind, TokenKind::Identifier(_))
            }) {
                // Parse inline binding: val name = expr or var name = expr
                self.advance(); // consume val/var
                let _binding_name = self.expect_identifier()?;
                self.expect(&TokenKind::Assign)?;
                let _binding_value = self.parse_expression()?;
                // Skip newlines/indent/dedent after binding
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                    || matches!(&self.current.kind, TokenKind::DocComment(_))
                {
                    self.advance();
                }
                // If there's no comma and not RParen, that's okay — the binding is just skipped
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                        || matches!(&self.current.kind, TokenKind::DocComment(_))
                    {
                        self.advance();
                    }
                }
                continue;
            }

            // Check for named argument with '=' or ':' syntax
            // Also handles keywords used as argument names (from, type, etc.)
            let mut name = None;
            let maybe_name = match &self.current.kind {
                TokenKind::Identifier(id) => Some(id.clone()),
                // Allow all keywords that might appear as named argument names
                TokenKind::From => Some("from".to_string()),
                TokenKind::Type => Some("type".to_string()),
                TokenKind::As => Some("as".to_string()),
                TokenKind::In => Some("in".to_string()),
                TokenKind::Is => Some("is".to_string()),
                TokenKind::To => Some("to".to_string()),
                TokenKind::Var => Some("var".to_string()),
                TokenKind::Me => Some("me".to_string()),
                TokenKind::Self_ => Some("self".to_string()),
                TokenKind::Result => Some("result".to_string()),
                TokenKind::Old => Some("old".to_string()),
                TokenKind::Out => Some("out".to_string()),
                TokenKind::OutErr => Some("out_err".to_string()),
                TokenKind::Match => Some("match".to_string()),
                TokenKind::Context => Some("context".to_string()),
                TokenKind::Shared => Some("shared".to_string()),
                TokenKind::Static => Some("static".to_string()),
                TokenKind::Const => Some("const".to_string()),
                TokenKind::Extern => Some("extern".to_string()),
                TokenKind::Fn => Some("fn".to_string()),
                TokenKind::Let => Some("let".to_string()),
                TokenKind::New => Some("new".to_string()),
                TokenKind::Spawn => Some("spawn".to_string()),
                TokenKind::Move => Some("move".to_string()),
                TokenKind::Dyn => Some("dyn".to_string()),
                TokenKind::Loop => Some("loop".to_string()),
                TokenKind::For => Some("for".to_string()),
                TokenKind::While => Some("while".to_string()),
                TokenKind::If => Some("if".to_string()),
                TokenKind::Else => Some("else".to_string()),
                TokenKind::Return => Some("return".to_string()),
                TokenKind::Break => Some("break".to_string()),
                TokenKind::Continue => Some("continue".to_string()),
                TokenKind::Async => Some("async".to_string()),
                TokenKind::Await => Some("await".to_string()),
                TokenKind::Yield => Some("yield".to_string()),
                TokenKind::Impl => Some("impl".to_string()),
                TokenKind::Trait => Some("trait".to_string()),
                TokenKind::Struct => Some("struct".to_string()),
                TokenKind::Class => Some("class".to_string()),
                TokenKind::Enum => Some("enum".to_string()),
                TokenKind::Union => Some("union".to_string()),
                TokenKind::Actor => Some("actor".to_string()),
                TokenKind::Macro => Some("macro".to_string()),
                TokenKind::With => Some("with".to_string()),
                TokenKind::Export => Some("export".to_string()),
                TokenKind::Import => Some("import".to_string()),
                TokenKind::Alias => Some("alias".to_string()),
                TokenKind::Gpu => Some("gpu".to_string()),
                TokenKind::Mod => Some("mod".to_string()),
                TokenKind::Use => Some("use".to_string()),
                TokenKind::Unit => Some("unit".to_string()),
                TokenKind::Vec => Some("vec".to_string()),
                TokenKind::Pub => Some("pub".to_string()),
                TokenKind::Priv => Some("priv".to_string()),
                TokenKind::Super => Some("super".to_string()),
                TokenKind::Common => Some("common".to_string()),
                TokenKind::Invariant => Some("invariant".to_string()),
                TokenKind::Requires => Some("requires".to_string()),
                TokenKind::Ensures => Some("ensures".to_string()),
                TokenKind::Where => Some("where".to_string()),
                TokenKind::Case => Some("case".to_string()),
                TokenKind::Crate => Some("crate".to_string()),
                TokenKind::Auto => Some("auto".to_string()),
                TokenKind::Not => Some("not".to_string()),
                TokenKind::And => Some("and".to_string()),
                TokenKind::Or => Some("or".to_string()),
                TokenKind::True => Some("true".to_string()),
                TokenKind::False => Some("false".to_string()),
                TokenKind::Def => Some("def".to_string()),
                TokenKind::NotTo => Some("not_to".to_string()),
                TokenKind::Bitfield => Some("bitfield".to_string()),
                _ => None,
            };
            if let Some(id_clone) = maybe_name {
                // Peek ahead for '=' or ':' without consuming the stream
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Assign {
                    name = Some(id_clone);
                    self.advance(); // consume identifier/keyword
                    self.expect(&TokenKind::Assign)?; // consume '='
                } else if next.kind == TokenKind::Colon {
                    // Support colon syntax: name: value
                    name = Some(id_clone);
                    self.advance(); // consume identifier/keyword
                    self.expect(&TokenKind::Colon)?; // consume ':'
                } else {
                    // leave current untouched; pending_token already holds the peeked token
                }
            }

            let value = self.parse_expression()?;
            args.push(Argument { name, value });

            // Skip newlines, indent, dedent, doc comments after argument (for multi-line argument lists)
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
                || matches!(&self.current.kind, TokenKind::DocComment(_))
            {
                self.advance();
            }

            // Handle trailing `not` modifier before closing paren:
            // e.g., `collection.contains(item not)` means `not collection.contains(item)`
            if self.check(&TokenKind::Not) {
                self.advance(); // consume `not`
                // Wrap the last argument's value in a UnaryOp(Not) or just skip
                // For now, consume it — the call semantics are preserved well enough for parsing
            }

            if !self.check(&TokenKind::RParen) {
                // Allow trailing comma (comma followed by RParen)
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Skip newlines, indent, dedent after comma
                    // For DocComment: only skip if it's NOT followed by Comma/RParen (i.e., it's a comment, not a """...""" value)
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                        || (matches!(&self.current.kind, TokenKind::DocComment(_))
                            && !self.peek_is(&TokenKind::Comma)
                            && !self.peek_is(&TokenKind::RParen))
                    {
                        self.advance();
                    }
                } else if self.check(&TokenKind::RBracket) {
                    // Mismatched bracket: ] inside () — break out of argument loop
                    // The ] will be consumed by the outer slice expression parser
                    break;
                } else {
                    self.expect(&TokenKind::Comma)?;
                    // Skip newlines, indent, dedent after comma
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                        || (matches!(&self.current.kind, TokenKind::DocComment(_))
                            && !self.peek_is(&TokenKind::Comma)
                            && !self.peek_is(&TokenKind::RParen))
                    {
                        self.advance();
                    }
                }
            }
        }

        // Accept either RParen or RBracket (for mismatched bracket recovery)
        // This handles code like: type_name[8:func(arg, -1])
        if self.check(&TokenKind::RBracket) {
            self.advance(); // consume ] and treat as implicit ) + ]
        } else {
            self.expect(&TokenKind::RParen)?;
        }
        Ok(args)
    }

    /// Parse macro invocation arguments: !(args) or !{args} or ![args]
    pub(crate) fn parse_macro_args(&mut self) -> Result<Vec<MacroArg>, ParseError> {
        // Macros can use (), {}, or [] for their arguments
        let (_open, close) = if self.check(&TokenKind::LParen) {
            (TokenKind::LParen, TokenKind::RParen)
        } else if self.check(&TokenKind::LBrace) {
            (TokenKind::LBrace, TokenKind::RBrace)
        } else if self.check(&TokenKind::LBracket) {
            (TokenKind::LBracket, TokenKind::RBracket)
        } else {
            return Err(ParseError::unexpected_token(
                "'(', '{', or '['",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.advance(); // consume opening delimiter
        let mut args = Vec::new();

        while !self.check(&close) {
            // Try to parse as expression
            let expr = self.parse_expression()?;
            args.push(MacroArg::Expr(expr));

            if !self.check(&close) {
                // Allow comma or semicolon as separator
                if self.check(&TokenKind::Comma) || self.check(&TokenKind::Semicolon) {
                    self.advance();
                }
            }
        }

        self.expect(&close)?;
        Ok(args)
    }

    /// Parse comprehension clause: `for pattern in iterable [if condition]`
    /// Returns (pattern, iterable, condition)
    fn parse_comprehension_clause(
        &mut self,
    ) -> Result<(Pattern, Expr, Option<Box<Expr>>), ParseError> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        let condition = if self.check(&TokenKind::If) {
            self.advance();
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        Ok((pattern, iterable, condition))
    }

    /// Parse lambda body (params, colon, expression or block) with given move mode
    fn parse_lambda_body(&mut self, move_mode: MoveMode) -> Result<Expr, ParseError> {
        let params = self.parse_lambda_params()?;
        self.expect(&TokenKind::Colon)?;

        // Check if body is an indented block or inline expression.
        // NOTE: Do NOT manipulate bracket_depth here — it corrupts the indent_stack
        // and causes regressions in files like infer.spl, cuda_type_mapper.spl, etc.
        let body = if self.check(&TokenKind::Newline) {
            if self.peek_is(&TokenKind::Indent) {
                let block = self.parse_block()?;
                Expr::DoBlock(block.statements)
            } else {
                // Multi-line lambda body inside brackets (INDENT suppressed).
                // Parse multiple items until we see a closing bracket or comma
                // at the same bracket depth.
                let saved_depth = self.lexer.bracket_depth;
                self.advance(); // consume the Newline
                // Skip leading newlines
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                let mut stmts = Vec::new();
                loop {
                    // Stop if we see closing bracket at our depth or less, comma at our depth, or Eof
                    if self.is_at_end() {
                        break;
                    }
                    match &self.current.kind {
                        TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
                            if self.lexer.bracket_depth <= saved_depth =>
                        {
                            break;
                        }
                        TokenKind::Comma if self.lexer.bracket_depth <= saved_depth => {
                            break;
                        }
                        TokenKind::Dedent => {
                            self.advance();
                            continue;
                        }
                        _ => {}
                    }
                    let item = self.parse_item()?;
                    stmts.push(item);
                    // Skip newlines between items
                    while self.check(&TokenKind::Newline) || self.check(&TokenKind::Semicolon) {
                        self.advance();
                    }
                }
                if stmts.len() == 1 {
                    if let Some(crate::ast::Node::Expression(expr)) = stmts.into_iter().next() {
                        expr
                    } else {
                        Expr::Nil
                    }
                } else {
                    Expr::DoBlock(stmts)
                }
            }
        } else if self.check(&TokenKind::LBrace) {
            // Could be dict literal `\: {"key": "val"}` or brace-delimited block `\: { stmt; expr }`
            // Peek ahead: if the token immediately after `{` is a string literal, treat as dict expression
            // Otherwise, treat as block body
            let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
            self.pending_token = Some(next.clone());
            let is_dict = matches!(next.kind,
                // {"key": val} - string key means dict literal
                TokenKind::String(_) | TokenKind::FString(_) | TokenKind::RawString(_)
                // {} - empty braces = empty dict/expression
                | TokenKind::RBrace
            );
            if is_dict {
                // Parse as expression (dict literal)
                self.parse_expression()?
            } else {
                // Brace-delimited block: \: { stmt1; stmt2; expr }
                self.advance(); // consume '{'
                self.skip_whitespace_tokens();
                let mut stmts = Vec::new();
                while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                    self.skip_whitespace_tokens();
                    if self.check(&TokenKind::RBrace) { break; }
                    let item = self.parse_item()?;
                    stmts.push(item);
                    while self.check(&TokenKind::Semicolon) || self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Expr::DoBlock(stmts)
            }
        } else {
            // Inline expression (same line)
            self.parse_expression()?
        };

        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode,
        })
    }

    /// Create a slice expression with the given components
    #[allow(dead_code)]
    fn make_slice(
        receiver: Expr,
        start: Option<Expr>,
        end: Option<Expr>,
        step: Option<Box<Expr>>,
    ) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }
    /// Try to parse generic type suffix: `<TypeArg1, TypeArg2, ...>` after an Identifier.
    /// Returns true if successfully parsed (modifying `expr` in place), false otherwise.
    /// Used for patterns like `Dict<i64, DefUseChain>.new()`.
    fn try_parse_generic_type_suffix(&mut self, expr: &mut Expr) -> bool {
        // We need to speculatively parse. Since we can't easily backtrack,
        // we'll use a heuristic: scan forward from `<` counting depth of `<>` brackets,
        // checking that we only see type-like tokens (identifiers, commas, brackets).
        // If we reach a matching `>` followed by `.` or `(`, it's generic args.

        // Save parser state for backtracking
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_token.clone();

        // Try to parse generic args
        self.advance(); // consume `<`
        let mut depth = 1i32;
        let mut type_names = Vec::new();
        let mut current_name = String::new();
        let mut valid = true;

        loop {
            match &self.current.kind {
                TokenKind::Lt => {
                    depth += 1;
                    current_name.push('<');
                    self.advance();
                }
                TokenKind::Gt => {
                    depth -= 1;
                    if depth == 0 {
                        if !current_name.is_empty() {
                            type_names.push(current_name.trim().to_string());
                        }
                        self.advance(); // consume `>`
                        break;
                    }
                    current_name.push('>');
                    self.advance();
                }
                TokenKind::Comma if depth == 1 => {
                    if !current_name.is_empty() {
                        type_names.push(current_name.trim().to_string());
                        current_name = String::new();
                    }
                    self.advance();
                }
                TokenKind::Identifier(name) => {
                    current_name.push_str(name);
                    self.advance();
                }
                // Allow types like i64, u8, etc. (these are identifiers but also used as types)
                TokenKind::Integer(_) => {
                    // Could be part of type like i64 - append the number text
                    let n = self.current.lexeme.clone();
                    current_name.push_str(&n);
                    self.advance();
                }
                TokenKind::LBracket => {
                    // Array types like [u8]
                    current_name.push('[');
                    self.advance();
                }
                TokenKind::RBracket => {
                    current_name.push(']');
                    self.advance();
                }
                TokenKind::Dot => {
                    // Qualified type names
                    current_name.push('.');
                    self.advance();
                }
                TokenKind::Newline | TokenKind::Eof | TokenKind::Assign
                | TokenKind::Indent | TokenKind::Dedent => {
                    // These shouldn't appear in generic type args
                    valid = false;
                    break;
                }
                _ => {
                    // Unknown token in generic args
                    valid = false;
                    break;
                }
            }
        }

        // Check if the parse succeeded and is followed by `.` or `(`
        if valid && depth == 0 && (self.check(&TokenKind::Dot) || self.check(&TokenKind::LParen)) {
            // Successfully parsed generic type args
            if let Expr::Identifier(name) = expr {
                let generic_name = format!("{}<{}>", name, type_names.join(", "));
                *expr = Expr::Identifier(generic_name);
            }
            true
        } else {
            // Backtrack
            self.current = saved_current;
            self.previous = saved_previous;
            self.pending_token = saved_pending;
            false
        }
    }

    /// Parse a function lambda body: handles block form (with INDENT), multi-line
    /// inside brackets (INDENT suppressed), and inline expression.
    pub(crate) fn parse_fn_lambda_body(&mut self) -> Result<Expr, ParseError> {
        if self.check(&TokenKind::Newline) {
            if self.peek_is(&TokenKind::Indent) {
                let block = self.parse_block()?;
                Ok(Expr::DoBlock(block.statements))
            } else {
                // Multi-line body inside brackets (INDENT suppressed).
                let saved_depth = self.lexer.bracket_depth;
                self.advance(); // consume the Newline
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                let mut stmts = Vec::new();
                loop {
                    if self.is_at_end() {
                        break;
                    }
                    match &self.current.kind {
                        TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
                            if self.lexer.bracket_depth <= saved_depth =>
                        {
                            break;
                        }
                        TokenKind::Comma if self.lexer.bracket_depth <= saved_depth => {
                            break;
                        }
                        TokenKind::Dedent => {
                            self.advance();
                            continue;
                        }
                        _ => {}
                    }
                    let item = self.parse_item()?;
                    stmts.push(item);
                    while self.check(&TokenKind::Newline) || self.check(&TokenKind::Semicolon) {
                        self.advance();
                    }
                }
                if stmts.len() == 1 {
                    if let Some(crate::ast::Node::Expression(expr)) = stmts.into_iter().next() {
                        Ok(expr)
                    } else {
                        Ok(Expr::Nil)
                    }
                } else {
                    Ok(Expr::DoBlock(stmts))
                }
            }
        } else {
            self.parse_expression()
        }
    }
}

// Primary expression parsing (extracted for maintainability)
include!("primary.rs");
