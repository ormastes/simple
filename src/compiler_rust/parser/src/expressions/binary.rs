use crate::ast::{BinOp, Expr, UnaryOp};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

/// Macro to generate binary operator parsing functions.
/// Reduces duplication in precedence-climbing parser.
///
/// Handles line continuation in two ways:
/// 1. Trailing operator: `expr +\n  expr` - skips newline/indent after operator
/// 2. Leading operator: `expr\n  + expr` - peeks through newline/indent to find operator
macro_rules! parse_binary_single {
    ($fn_name:ident, $next_fn:ident, $token:ident, $op:expr) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            loop {
                if self.check(&TokenKind::$token) {
                    // Case 1: trailing operator on this line
                    self.advance();
                    self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                } else if self.peek_through_newlines_and_indents_is(&TokenKind::$token) {
                    // Case 2: operator on next line (leading continuation)
                    self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                    self.advance(); // consume the operator
                    self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                } else {
                    break;
                }
                let right = self.$next_fn()?;
                left = Expr::Binary {
                    op: $op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
            Ok(left)
        }
    };
}

/// Macro for binary operators with multiple token options.
///
/// Handles line continuation in two ways:
/// 1. Trailing operator: `expr +\n  expr` - skips newline/indent after operator
/// 2. Leading operator: `expr\n  + expr` - peeks through newline/indent to find operator
///
/// `indent_required` variant: the leading-continuation lookahead only fires when
/// the operator sits on a MORE DEEPLY INDENTED line. Required for `+`/`-`, which
/// are also legal statement starts — see `parse_term`.
macro_rules! parse_binary_multi {
    (indent_required $fn_name:ident, $next_fn:ident, $( $token:ident => $op:expr ),+ $(,)?) => {
        parse_binary_multi!(@impl $fn_name, $next_fn, peek_indented_operator_continuation,
            $( $token => $op ),+);
    };
    ($fn_name:ident, $next_fn:ident, $( $token:ident => $op:expr ),+ $(,)?) => {
        parse_binary_multi!(@impl $fn_name, $next_fn, peek_through_newlines_and_indents,
            $( $token => $op ),+);
    };
    (@impl $fn_name:ident, $next_fn:ident, $peek_fn:ident, $( $token:ident => $op:expr ),+ $(,)?) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            loop {
                // Try to match operator at current position first
                let op = match &self.current.kind {
                    $( TokenKind::$token => Some($op), )+
                    _ => None,
                };
                if let Some(op) = op {
                    // Case 1: trailing operator on this line
                    self.advance();
                    self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                    let right = self.$next_fn()?;
                    left = Expr::Binary {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    };
                    continue;
                }
                // Case 2: operator on next line (leading continuation)
                // Only check if current token is Newline or Indent
                if matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
                    let found_op = {
                        let peeked = self.$peek_fn();
                        match peeked {
                            $( Some(TokenKind::$token) => Some($op), )+
                            _ => None,
                        }
                    };
                    if let Some(op) = found_op {
                        self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                        self.advance(); // consume the operator
                        self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                        let right = self.$next_fn()?;
                        left = Expr::Binary {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        };
                        continue;
                    }
                }
                break;
            }
            Ok(left)
        }
    };
}

impl<'a> Parser<'a> {
    // Binary expression parsing with precedence (using macros to reduce duplication)
    // Precedence (lowest to highest): pipe, compose/layer_connect, parallel, or, and, equality, comparison, bitwise_or, bitwise_xor, bitwise_and, shift, term, factor, power

    // Pipeline operator |> (lowest precedence - passes value to function)
    parse_binary_single!(parse_pipe, parse_compose, PipeForward, BinOp::PipeForward);

    // LayerConnect ~> operator (between pipe and parallel)
    // ~> = ML layer composition (neural network layer connection)
    // Note: >> is parsed as ShiftRight at the shift precedence level (line 302).
    // Function composition uses |> (pipe) instead.
    parse_binary_single!(parse_compose, parse_parallel, TildeArrow, BinOp::LayerConnect);

    // Parallel operator // (executes functions in parallel)
    parse_binary_single!(parse_parallel, parse_or, Parallel, BinOp::Parallel);

    // Logical operators (support both keyword and symbol forms: or/||, and/&&)
    // Also supports suspension variants: and~, or~ (awaits RHS before evaluation)
    parse_binary_multi!(parse_or, parse_and,
        Or => BinOp::Or,
        DoublePipe => BinOp::Or,
        OrSuspend => BinOp::OrSuspend,
    );
    parse_binary_multi!(parse_and, parse_equality,
        And => BinOp::And,
        DoubleAmp => BinOp::And,
        AndSuspend => BinOp::AndSuspend,
    );
    // Bitwise OR: `|`. Hand-written instead of parse_binary_single! (task #184):
    // grid literals reuse `|` as the row/cell delimiter (`grid:\n    | 1 | 2 |`).
    // While parsing a grid row's cell expression (`grid_row_depth > 0`, set by
    // `parse_grid_rows` in expressions/primary/math.rs), a `|` must close the
    // cell/row instead of being consumed as a continuing BitOr operand — see
    // `grid_literal_remains_contextual`.
    pub(crate) fn parse_bitwise_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_bitwise_xor()?;
        if self.grid_row_depth > 0 {
            return Ok(left);
        }
        loop {
            if self.check(&TokenKind::Pipe) {
                // Case 1: trailing operator on this line
                self.advance();
                self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
            } else if self.peek_through_newlines_and_indents_is(&TokenKind::Pipe) {
                // Case 2: operator on next line (leading continuation)
                self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                self.advance(); // consume the operator
                self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
            } else {
                break;
            }
            let right = self.parse_bitwise_xor()?;
            left = Expr::Binary {
                op: BinOp::BitOr,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }
    parse_binary_single!(parse_bitwise_xor, parse_bitwise_and, Xor, BinOp::BitXor);
    parse_binary_single!(parse_bitwise_and, parse_shift, Ampersand, BinOp::BitAnd);

    /// Step over a line break when the next meaningful token is a leading
    /// COMPARISON/EQUALITY-family operator on a *strictly more deeply
    /// indented* line (`a\n    == b`).
    ///
    /// `parse_equality` and `parse_comparison` are hand-written (for `not in`
    /// and for `a < b < c` chaining) and so never inherited the
    /// `parse_binary_*!` macros' "Case 2" leading-continuation arm; they only
    /// ever got the TRAILING-form fix from 023a60a05aa. That left the seed
    /// rejecting `== != < > <= >= is in` as leading continuations while the
    /// self-hosted parser accepted them — see doc/08_tracking/bug/
    /// parser_leading_operator_line_continuation_2026-08-01.md.
    ///
    /// The deeper-indent requirement mirrors the self-hosted
    /// `leading_op_continues` rule and the `indent_required` variant of
    /// `parse_binary_multi!` above: it is what stops a same-indent statement
    /// from being swallowed into the previous expression. It is enforced via
    /// `peek_indented_operator_continuation`, which also returns `None` on a
    /// `Dedent`, so a shallower line can never continue an expression either.
    ///
    /// `not in` is deliberately absent: bare `not` is a legal statement start,
    /// so accepting a leading `not` would glue a following `not ...` statement
    /// onto the previous expression — exactly the class of silent misparse the
    /// indent guard exists to prevent (guard 3 of the self-hosted rule).
    fn skip_leading_comparison_continuation(&mut self) {
        if !matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
            return;
        }
        let is_family = matches!(
            self.peek_indented_operator_continuation(),
            Some(
                TokenKind::Eq
                    | TokenKind::NotEq
                    | TokenKind::Is
                    | TokenKind::In
                    | TokenKind::Lt
                    | TokenKind::Gt
                    | TokenKind::LtEq
                    | TokenKind::GtEq
            )
        );
        if is_family {
            self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
        }
    }

    // Equality and membership operators (manual for `not in` support)
    pub(crate) fn parse_equality(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;
        loop {
            // Case 2: leading-operator line continuation (`a\n    == b`).
            // No-op when an operator is already the current token.
            self.skip_leading_comparison_continuation();
            let kind = self.current.kind.clone();
            let op = match &kind {
                TokenKind::Eq => BinOp::Eq,
                TokenKind::NotEq => BinOp::NotEq,
                TokenKind::Is => BinOp::Is,
                TokenKind::In => BinOp::In,
                TokenKind::Not if self.peek_is(&TokenKind::In) => {
                    self.advance(); // consume 'not'
                    BinOp::NotIn
                }
                _ => break,
            };
            self.advance();
            // Trailing-operator line continuation (`a ==\n    b`). This
            // function is hand-written rather than generated by
            // `parse_binary_single!` (it has to special-case `not in`), so it
            // never inherited the macro's continuation handling and equality
            // continuations failed with "expected expression, found Newline"
            // in EVERY context — `val` bindings as much as `if` conditions.
            // See doc/08_tracking/bug/
            // if_condition_operator_line_continuation_parse_2026-07-30.md.
            self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
            let right = self.parse_comparison()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    /// Parse comparisons with chaining support: a < b < c becomes (a < b) and (b < c)
    pub(crate) fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_range()?;

        // Case 2: leading-operator line continuation (`a\n    < b`). This must
        // run BEFORE the "is there a comparison at all?" probe below —
        // otherwise the probe sees a `Newline`, returns `left` untouched, and
        // the continuation is never reachable.
        self.skip_leading_comparison_continuation();

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

        loop {
            // Keep chained comparisons (`a\n    < b\n    < c`) continuable.
            // No-op on the first iteration: `current` is already the operator.
            self.skip_leading_comparison_continuation();
            let op = match &self.current.kind {
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::LtEq => BinOp::LtEq,
                TokenKind::GtEq => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            // Trailing-operator line continuation (`a >\n    b`). Same gap as
            // in `parse_equality` above: this function is hand-written (to
            // support comparison chaining `a < b < c`) and so never inherited
            // `parse_binary_single!`'s continuation handling.
            self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
            let right = self.parse_range()?;

            comparisons.push(Expr::Binary {
                op,
                left: Box::new(prev_right.clone()),
                right: Box::new(right.clone()),
            });

            prev_right = right;
        }

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

    /// Parse range expressions: a..b (exclusive), a..=b (inclusive), a.. (suffix), ..b (prefix), or .. (full)
    pub(crate) fn parse_range(&mut self) -> Result<Expr, ParseError> {
        use crate::ast::RangeBound;

        // Check for prefix range (..end or ..=end) first - no start expression
        if self.check(&TokenKind::DoubleDotEq) {
            self.advance();
            let end = if self.is_range_terminator() {
                None
            } else {
                Some(Box::new(self.parse_bitwise_or()?))
            };
            return Ok(Expr::Range {
                start: None,
                end,
                bound: RangeBound::Inclusive,
            });
        }

        if self.check(&TokenKind::DoubleDot) {
            self.advance();
            let end = if self.is_range_terminator() {
                None
            } else {
                Some(Box::new(self.parse_bitwise_or()?))
            };
            return Ok(Expr::Range {
                start: None,
                end,
                bound: RangeBound::Exclusive,
            });
        }

        // Regular range with start expression
        let start = self.parse_bitwise_or()?;

        // Check for range operators
        let bound = if self.check(&TokenKind::DoubleDotEq) {
            Some(RangeBound::Inclusive)
        } else if self.check(&TokenKind::DoubleDot) {
            Some(RangeBound::Exclusive)
        } else {
            None
        };

        if let Some(bound) = bound {
            self.advance(); // consume '..' or '..='

            // Check if there's an end expression or if this is a half-open range (e.g., `offset..`)
            // Tokens that can't start an expression indicate a half-open range
            let end = if self.is_range_terminator() {
                None
            } else {
                Some(Box::new(self.parse_bitwise_or()?))
            };

            Ok(Expr::Range {
                start: Some(Box::new(start)),
                end,
                bound,
            })
        } else {
            Ok(start)
        }
    }

    /// Check if current token terminates a range expression (can't start an expression)
    fn is_range_terminator(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::RBracket
                | TokenKind::RParen
                | TokenKind::RBrace
                | TokenKind::Comma
                | TokenKind::Colon
                | TokenKind::Semicolon
                | TokenKind::Newline
                | TokenKind::Dedent
                | TokenKind::Eof
        )
    }

    // Bitwise shift operators: << (left) and >> (right)
    parse_binary_multi!(parse_shift, parse_matmul,
        ShiftLeft => BinOp::ShiftLeft,
        ShiftRight => BinOp::ShiftRight,
    );

    // Simple Math: Matrix multiplication @ operator (#1930-#1939)
    // Precedence: between shift and term (same level as factor: *, /, %, //)
    // NOTE: Hand-written instead of parse_binary_single! because @ must NOT
    // peek through newlines — `val x = 16\n@gpu_kernel fn...` would otherwise
    // be parsed as `x = 16 @ gpu_kernel` (matmul) instead of a decorator.
    pub(crate) fn parse_matmul(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_term()?;
        loop {
            if self.check(&TokenKind::At) {
                // Only trailing @: `a @ b` on same line
                self.advance();
                self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                let right = self.parse_term()?;
                left = Expr::Binary {
                    op: BinOp::MatMul,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    // Additive operators: `+` and `-`. `indent_required` because these are the
    // only binary operators that are also legal STATEMENT starts (unary sign).
    // A same-indent `-1` line after `return 15` is a new statement, not a
    // continuation — gluing it produced `return (15 - 1)` == 14.
    parse_binary_multi!(indent_required parse_term, parse_factor,
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
    );

    parse_binary_multi!(parse_factor, parse_power,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Mod,
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
            TokenKind::Minus => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Not | TokenKind::Bang => {
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
            TokenKind::ChannelArrow => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::ChannelRecv,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Move => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Move,
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
                    let operand = self.parse_expression()?;
                    Ok(Expr::Yield(Some(Box::new(operand))))
                }
            }
            _ => self.parse_postfix(),
        }
    }
}

#[cfg(test)]
mod comparison_continuation_tests {
    /// Trailing-operator line continuation must work for COMPARISON and
    /// EQUALITY operators, not just the `parse_binary_single!`-generated ones.
    ///
    /// `parse_comparison` and `parse_equality` are hand-written (for `a < b < c`
    /// chaining and `not in` respectively) and never inherited the macro's
    /// continuation handling, so `a >\n  b` failed with "expected expression,
    /// found Newline" in EVERY context — `val` bindings as much as `if`
    /// conditions. It blocked the whole host-WM evidence gate via
    /// src/lib/common/web/browser_renderer_protocol.spl:559.
    ///
    /// See doc/08_tracking/bug/
    /// if_condition_operator_line_continuation_parse_2026-07-30.md.
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    #[test]
    fn comparison_operator_line_continuation_parses() {
        // The exact shape that blocked the gate: method-call LHS, comparison
        // operator at end of line, arithmetic RHS on the next line.
        assert!(
            parses("fn f(p: [i64], cap: i64) -> bool:\n    val m = 100\n    if p.len().to_i64() >\n       m - cap:\n        return true\n    false\n"),
            "real-world `if <call> >\\n  <expr>:` must parse"
        );
        for op in ["<", ">", "<=", ">="] {
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> bool:\n    val x = a {op}\n       b\n    x\n")),
                "binding continuation after `{op}` must parse"
            );
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> bool:\n    if a {op}\n       b:\n        return true\n    false\n")),
                "if-condition continuation after `{op}` must parse"
            );
        }
    }

    #[test]
    fn equality_operator_line_continuation_parses() {
        for op in ["==", "!="] {
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> bool:\n    val x = a {op}\n       b\n    x\n")),
                "binding continuation after `{op}` must parse"
            );
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> bool:\n    if a {op}\n       b:\n        return true\n    false\n")),
                "if-condition continuation after `{op}` must parse"
            );
        }
    }

    #[test]
    fn while_condition_comparison_continuation_parses() {
        assert!(
            parses("fn f(a: i64, b: i64) -> i64:\n    var i = 0\n    while a >\n          b:\n        i = i + 1\n        break\n    i\n"),
            "while-condition continuation after `>` must parse"
        );
    }

    /// Sibling forms that already worked (macro-generated operators) — kept so
    /// a future refactor of the macro cannot silently regress them.
    #[test]
    fn arithmetic_and_logical_continuation_still_parse() {
        assert!(parses("fn g(a: i64, b: i64) -> i64:\n    val x = a +\n       b\n    x\n"));
        assert!(parses("fn h(a: bool, b: bool) -> bool:\n    if a and\n       b:\n        return true\n    false\n"));
        assert!(parses("fn i(a: bool, b: bool) -> bool:\n    if a or\n       b:\n        return true\n    false\n"));
    }

    /// Keep the bootstrap parser aligned with the pure-Simple G27b leading
    /// operator rule.  Stage 2 once ended the condition at `first` and
    /// reported `expected :, got Newline` before reaching the leading `and`.
    #[test]
    fn leading_logical_if_continuation_and_grouped_control_parse() {
        let leading = "fn f(first: bool, second: bool) -> bool:\n    if first\n        and second:\n        return true\n    false\n";
        let grouped = "fn f(first: bool, second: bool) -> bool:\n    if (first\n        and second):\n        return true\n    false\n";
        assert!(parses(leading), "leading `and` condition continuation must parse");
        assert!(parses(grouped), "parenthesized recovery form must parse");
    }

    /// `elif`'s own statement-level indent bookkeeping was fixed (see
    /// `elif_condition_continuation_parses` below): `parse_if`'s `elif`/`else
    /// if` loops in `control_flow.rs` were missing the
    /// save-before/drain-after `deferred_dedent_count` dance that the primary
    /// `if` block-style path already applies around `parse_block()`, so a
    /// multi-line `elif` condition leaked a stray `Dedent` token into the
    /// stream and broke parsing of everything after it. That is now applied
    /// consistently across all four `elif`/`else if` call sites via
    /// `parse_elif_or_else_if_body`.
    ///
    /// FLIPPED (see doc/08_tracking/bug/
    /// seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md):
    /// this specific repro was previously pinned as still-broken because it
    /// hits the DEEP continuation shape (continuation column > following
    /// block body column), which neither `if`'s nor `elif`'s old "drain after
    /// the block" strategy resolved correctly (only `while`'s old "drain
    /// immediately after the condition's Newline" strategy did, and that in
    /// turn broke the opposite, shallow shape). `parse_condition_block`
    /// (`parser_impl/core.rs`) now drains at BOTH candidate points — before
    /// the block's own Indent and after the block body — so both shapes
    /// parse regardless of which one produced the compensating DEDENT. See
    /// `condition_continuation_indent_shape_matrix` below for the full
    /// {if, elif, else if, while, for, match} × {deep, shallow, equal} probe
    /// matrix. Non-vacuity was verified manually by reverting
    /// `parse_condition_block`/`drain_available_deferred_dedents` and
    /// confirming this and the matrix's deep/shallow cells reproduce the
    /// exact `UnexpectedToken` shapes documented in the bug writeup.
    #[test]
    fn elif_condition_deep_continuation_indent_ambiguity_is_now_supported() {
        assert!(
            parses("fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a >\n         b:\n        return 2\n    3\n"),
            "the shared if/elif deep-continuation indent ambiguity must be fixed by parse_condition_block"
        );
    }

    /// The `elif`-specific fix: multi-line `elif`/`else if` conditions now
    /// parse, for comparison, equality, and logical operators, as long as the
    /// continuation line is NOT indented deeper than the branch body (the
    /// shape the primary `if` block-style path already supported before this
    /// fix — see `elif_condition_deep_continuation_indent_ambiguity_is_still_unsupported`
    /// above for the still-open deeper-continuation shape).
    ///
    /// Non-vacuity: every assertion here fails with `UnexpectedToken { found:
    /// "Dedent", .. }` on the pre-fix `control_flow.rs` (verified by
    /// temporarily reverting the `parse_elif_or_else_if_body` call sites back
    /// to a bare `self.parse_inline_or_block()?`).
    #[test]
    fn elif_condition_continuation_parses() {
        for op in ["<", ">", "<=", ">="] {
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a {op}\n       b:\n        return 2\n    3\n")),
                "elif-condition continuation after `{op}` must parse"
            );
        }
        for op in ["==", "!="] {
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a {op}\n       b:\n        return 2\n    3\n")),
                "elif-condition continuation after `{op}` must parse"
            );
        }
        assert!(
            parses("fn f(a: bool, b: bool) -> i64:\n    if a and b:\n        return 1\n    elif a and\n        b:\n        return 2\n    3\n"),
            "elif-condition continuation after `and` must parse"
        );
        assert!(
            parses("fn f(a: bool, b: bool) -> i64:\n    if a and b:\n        return 1\n    elif a or\n        b:\n        return 2\n    3\n"),
            "elif-condition continuation after `or` must parse"
        );
        // `else if` (not the `elif` keyword) goes through a separate call site
        // in control_flow.rs — must be covered too.
        assert!(
            parses("fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    else if a >\n       b:\n        return 2\n    3\n"),
            "else-if-condition continuation must parse"
        );
        // A second `elif` in a chain exercises the loop re-entry, not just
        // the first iteration.
        assert!(
            parses("fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a == 0:\n        return 0\n    elif a >\n       b:\n        return 2\n    3\n"),
            "second elif in a chain must parse continuation"
        );
    }

    /// Sibling coverage for `while`, matching item 6 of the elif fix task:
    /// comparison (pre-existing, see `while_condition_comparison_continuation_parses`
    /// above), equality, and logical operators must all continue the
    /// condition across lines. Uses the same (deeper-than-body) continuation
    /// shape as the existing passing comparison test, since that is the shape
    /// `parse_while`'s "drain immediately after Newline" strategy supports —
    /// the opposite (shallower) shape is a separate open gap, see
    /// doc/08_tracking/bug/seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
    #[test]
    fn while_condition_equality_and_logical_continuation_parses() {
        for op in ["==", "!="] {
            assert!(
                parses(&format!("fn f(a: i64, b: i64) -> i64:\n    var i = 0\n    while a {op}\n          b:\n        i = i + 1\n        break\n    i\n")),
                "while-condition continuation after `{op}` must parse"
            );
        }
        assert!(
            parses("fn f(a: bool, b: bool) -> i64:\n    var i = 0\n    while a and\n           b:\n        i = i + 1\n        break\n    i\n"),
            "while-condition continuation after `and` must parse"
        );
        assert!(
            parses("fn f(a: bool, b: bool) -> i64:\n    var i = 0\n    while a or\n           b:\n        i = i + 1\n        break\n    i\n"),
            "while-condition continuation after `or` must parse"
        );
    }

    /// Build a probe source exercising condition-continuation dedent
    /// handling for a given statement `keyword`, at a given continuation
    /// column (`cont_col`, the column of the continuation line's second
    /// operand) and block-body column (`body_col`, the column of the first
    /// token of the following block):
    /// - deep:    cont_col > body_col
    /// - shallow: cont_col < body_col
    /// - equal:   cont_col == body_col
    fn condition_continuation_probe(keyword: &str, cont_col: usize, body_col: usize) -> String {
        let cont = " ".repeat(cont_col);
        let body = " ".repeat(body_col);
        match keyword {
            "if" => format!("fn f(a: i64, b: i64) -> i64:\n    if a >\n{cont}b:\n{body}return 2\n    3\n"),
            "elif" => format!(
                "fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a >\n{cont}b:\n{body}return 2\n    3\n"
            ),
            "else if" => format!(
                "fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    else if a >\n{cont}b:\n{body}return 2\n    3\n"
            ),
            "while" => format!(
                "fn f(a: i64, b: i64) -> i64:\n    var i = 0\n    while a >\n{cont}b:\n{body}i = i + 1\n    i\n"
            ),
            "for" => format!(
                "fn f(a: [i64], b: [i64]) -> i64:\n    var s = 0\n    for x in a +\n{cont}b:\n{body}s = s + x\n    s\n"
            ),
            "match" => format!(
                "fn f(a: i64, b: i64) -> i64:\n    match a +\n{cont}b:\n{body}case 0 -> 1\n{body}case _ -> 2\n"
            ),
            _ => unreachable!("unknown keyword {keyword}"),
        }
    }

    /// Full probe matrix for the unified condition-continuation dedent fix:
    /// {if, elif, else if, while, for, match} × {deep, shallow, equal}. See
    /// doc/08_tracking/bug/
    /// seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md
    /// for the mechanism and the pre-fix per-shape coverage of each site
    /// (before this fix: `if`/`elif`/`else if` only handled shallow, `while`
    /// only handled deep, and `for`/`match` handled neither — see individual
    /// call sites in `control_flow.rs`). All nine cells below must parse
    /// after `parse_condition_block`/`drain_available_deferred_dedents`.
    ///
    /// Column choices mirror the exact reproductions in the bug doc: deep =
    /// (9, 8), shallow = (7, 8), equal = (8, 8) — all deeper than the
    /// statement's own column (4), so a pseudo-INDENT is genuinely consumed
    /// during condition parsing in every cell.
    #[test]
    fn condition_continuation_indent_shape_matrix() {
        let keywords = ["if", "elif", "else if", "while", "for", "match"];
        let shapes: [(&str, usize, usize); 3] = [("deep", 9, 8), ("shallow", 7, 8), ("equal", 8, 8)];

        let mut failures = Vec::new();
        for keyword in keywords {
            for (shape_name, cont_col, body_col) in shapes {
                let src = condition_continuation_probe(keyword, cont_col, body_col);
                if !parses(&src) {
                    failures.push(format!("{keyword} / {shape_name} (cont={cont_col}, body={body_col})"));
                }
            }
        }

        assert!(
            failures.is_empty(),
            "condition-continuation indent matrix has {} failing cell(s):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}
