//! Parser helper methods - utility functions for tokenization, expectations, and generic parsing

use std::collections::HashMap;

use super::*;
use crate::ast::{BinOp, UnaryOp};
use crate::error_recovery::{detect_common_mistake, ErrorHint, ErrorHintLevel};
use crate::macro_registry::ConstValue;

impl<'a> Parser<'a> {
    pub(crate) fn advance(&mut self) {
        // Detect common mistakes before advancing
        // Skip check if this is the very first advance (previous == EOF) because
        // the initial token was already checked in Parser::new()
        let skip_check = matches!(self.previous.kind, TokenKind::Eof);

        let next_token = if !self.pending_tokens.is_empty() {
            Some(&self.pending_tokens[0])
        } else {
            None
        };

        if !skip_check {
            if let Some(mistake) = detect_common_mistake(&self.current, &self.previous, next_token)
            {
                // Determine error hint level based on mistake type
                use crate::error_recovery::CommonMistake;
                let level = match mistake {
                    // Errors for wrong keywords/syntax
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

                    // Warnings for verbose but valid syntax
                    CommonMistake::VerboseReturnType
                    | CommonMistake::ExplicitSelf
                    | CommonMistake::WrongBrackets
                    | CommonMistake::CSemicolon
                    | CommonMistake::SemicolonAfterBlock => ErrorHintLevel::Warning,

                    // Info for style preferences
                    CommonMistake::TsLet | CommonMistake::PythonSelf | CommonMistake::RustFnMut => {
                        ErrorHintLevel::Info
                    }

                    // Hints for advanced features
                    CommonMistake::RustLifetime
                    | CommonMistake::RustMacro
                    | CommonMistake::RustTurbofish
                    | CommonMistake::TsArrowFunction
                    | CommonMistake::PythonElif => ErrorHintLevel::Hint,
                };

                let hint = ErrorHint {
                    level,
                    message: format!("Common mistake detected: {}", mistake.suggestion()),
                    span: self.current.span.clone(),
                    suggestion: Some(mistake.suggestion()),
                    help: Some(mistake.message()),
                };

                self.error_hints.push(hint);
            }
        }

        self.previous = std::mem::replace(
            &mut self.current,
            self.pending_tokens
                .pop_front()
                .unwrap_or_else(|| self.lexer.next_token()),
        );
    }

    pub(crate) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current.kind) == std::mem::discriminant(kind)
    }

    pub(crate) fn is_at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    /// Peek at the next token without consuming current
    pub(crate) fn peek_is(&mut self, kind: &TokenKind) -> bool {
        // Save current state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        // Advance to peek
        self.advance();
        let result = self.check(kind);

        // Restore state - push current to front of pending tokens
        self.pending_tokens.push_front(self.current.clone());
        self.current = saved_current;
        self.previous = saved_previous;

        result
    }

    /// Peek through newlines to check if the next meaningful token matches.
    /// Used for multi-line method chaining:
    ///   - obj.method()\n.another()  (dot at same indentation level)
    ///
    /// Peeks through NEWLINE and INDENT tokens to find if a specific token follows.
    /// Used for multi-line method chaining where we need to see if a dot follows
    /// after newlines and indentation.
    pub(crate) fn peek_through_newlines_and_indents_is(&mut self, kind: &TokenKind) -> bool {
        let mut lookahead_pos = 0;

        // Look through existing pending_tokens and buffer more from lexer if needed
        loop {
            // Get the token at lookahead_pos
            let token = if lookahead_pos == 0 {
                &self.current
            } else if lookahead_pos <= self.pending_tokens.len() {
                &self.pending_tokens[lookahead_pos - 1]
            } else {
                // Need to buffer more tokens from lexer
                let tok = self.lexer.next_token();
                self.pending_tokens.push_back(tok);
                self.pending_tokens.back().unwrap()
            };

            match &token.kind {
                // Skip through NEWLINE and INDENT tokens for method chaining
                TokenKind::Newline | TokenKind::Indent => {
                    lookahead_pos += 1;
                }
                // DEDENT signals end of indented block - stop here
                TokenKind::Dedent => {
                    return false;
                }
                // Found a meaningful token - check if it's what we want
                _ => {
                    return std::mem::discriminant(&token.kind) == std::mem::discriminant(kind);
                }
            }

            // Safety limit to prevent infinite loops
            if lookahead_pos > 100 {
                return false;
            }
        }
    }

    /// Skip through newlines and indents when we've confirmed a dot follows.
    /// Used for multi-line method chaining.
    /// Call this AFTER peek_through_newlines_and_indents_is returns true.
    /// Returns the number of INDENT tokens skipped (need to consume matching DEDENTs later).
    pub(crate) fn skip_newlines_and_indents_for_method_chain(&mut self) -> usize {
        let mut indent_count = 0;
        while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
            if matches!(self.current.kind, TokenKind::Indent) {
                indent_count += 1;
            }
            self.advance();
        }
        indent_count
    }

    /// Consume DEDENT tokens to balance INDENTs consumed during method chaining.
    /// Also skips NEWLINEs before DEDENTs since they often appear between.
    pub(crate) fn consume_dedents_for_method_chain(&mut self, count: usize) {
        let mut remaining = count;
        while remaining > 0 {
            match &self.current.kind {
                TokenKind::Newline => {
                    self.advance();
                }
                TokenKind::Dedent => {
                    self.advance();
                    remaining -= 1;
                }
                _ => break,
            }
        }
    }

    /// Check if the next token after the current could start a type.
    /// Used to distinguish typed patterns (x: Int) from match arm separators (case x:).
    pub(crate) fn peek_is_type_start(&mut self) -> bool {
        // Save current state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        // Advance past colon to peek at what follows
        self.advance();

        // Check if this token could start a type expression
        let result = matches!(
            &self.current.kind,
            TokenKind::Identifier(_)
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::Fn
                | TokenKind::Mut
                | TokenKind::Dyn
                | TokenKind::Ampersand
        );

        // Restore state - push current to front of pending tokens
        self.pending_tokens.push_front(self.current.clone());
        self.current = saved_current;
        self.previous = saved_previous;

        result
    }

    /// Parse array with spread operators: [*a, 1, *b]
    pub(crate) fn parse_array_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut elements = Vec::new();

        while !self.check(&TokenKind::RBracket) {
            if self.check(&TokenKind::Star) {
                self.advance();
                elements.push(Expr::Spread(Box::new(self.parse_expression()?)));
            } else {
                elements.push(self.parse_expression()?);
            }
            if !self.check(&TokenKind::RBracket) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(Expr::Array(elements))
    }

    /// Parse dict with spread operators: {**d1, "key": value, **d2}
    pub(crate) fn parse_dict_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut pairs = Vec::new();

        while !self.check(&TokenKind::RBrace) {
            if self.check(&TokenKind::DoubleStar) {
                self.advance(); // **
                let spread_expr = self.parse_expression()?;
                pairs.push((Expr::DictSpread(Box::new(spread_expr)), Expr::Nil));
            } else {
                let key = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let value = self.parse_expression()?;
                pairs.push((key, value));
            }
            if !self.check(&TokenKind::RBrace) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Expr::Dict(pairs))
    }

    pub(crate) fn expect(&mut self, kind: &TokenKind) -> Result<(), ParseError> {
        if self.check(kind) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                format!("{:?}", kind),
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    pub(crate) fn expect_identifier(&mut self) -> Result<String, ParseError> {
        let name = match &self.current.kind {
            TokenKind::Identifier(name) => name.clone(),
            // Allow contract keywords to be used as identifiers (parameter names, variable names, etc.)
            // These are only keywords in specific contract contexts
            TokenKind::Result => "result".to_string(),
            TokenKind::Type => "type".to_string(),
            TokenKind::Out => "out".to_string(),
            TokenKind::OutErr => "out_err".to_string(),
            // Allow Gherkin keywords to be used as identifiers
            // These are only keywords at the start of BDD test statements
            TokenKind::Feature => "feature".to_string(),
            TokenKind::Scenario => "scenario".to_string(),
            TokenKind::Outline => "outline".to_string(),
            TokenKind::Examples => "examples".to_string(),
            TokenKind::Given => "given".to_string(),
            TokenKind::When => "when".to_string(),
            TokenKind::Then => "then".to_string(),
            TokenKind::AndThen => "and_then".to_string(),
            // Allow context keyword to be used as identifier in BDD DSL
            TokenKind::Context => "context".to_string(),
            // Allow 'default' to be used as trait name (e.g., Default trait)
            TokenKind::Default => "Default".to_string(),
            // Allow 'common' to be used as identifier (directory name in stdlib)
            TokenKind::Common => "common".to_string(),
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        };
        self.advance();
        Ok(name)
    }

    pub(crate) fn check_ident(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier(current) if current == name)
    }

    pub(crate) fn expect_ident_value(&mut self, name: &str) -> Result<(), ParseError> {
        if self.check_ident(name) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                name,
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Expect an identifier or a keyword that can be used as a path segment.
    /// This allows using reserved words like 'unit', 'test', etc. in module paths.
    pub(crate) fn expect_path_segment(&mut self) -> Result<String, ParseError> {
        // First try regular identifier
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }

        // Allow certain keywords as path segments
        let name = match &self.current.kind {
            TokenKind::Unit => "unit",
            TokenKind::Type => "type",
            TokenKind::As => "as",
            TokenKind::In => "in",
            TokenKind::Is => "is",
            TokenKind::Or => "or",
            TokenKind::And => "and",
            TokenKind::Not => "not",
            TokenKind::Mod => "mod",
            TokenKind::Use => "use",
            TokenKind::Match => "match",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::For => "for",
            TokenKind::While => "while",
            TokenKind::Loop => "loop",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::Return => "return",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::Crate => "crate", // Allow "crate" keyword in paths
            TokenKind::Result => "result", // Allow "result" keyword in paths
            TokenKind::To => "to",       // Allow "to" in paths (e.g., to_sdn)
            TokenKind::NotTo => "not_to", // Allow "not_to" in paths
            TokenKind::Context => "context", // Allow "context" in paths
            TokenKind::Feature => "feature", // Allow BDD keywords in paths
            TokenKind::Scenario => "scenario",
            TokenKind::Given => "given",
            TokenKind::When => "when",
            TokenKind::Then => "then",
            TokenKind::Old => "old",           // Allow "old" in paths
            TokenKind::Let => "let",           // Allow "let" in export statements
            TokenKind::Mock => "mock",         // Allow "mock" in export/path contexts
            TokenKind::AndThen => "and_then",  // Allow "and_then" in export statements
            TokenKind::Examples => "examples", // Allow "examples" in export statements
            TokenKind::Outline => "outline",   // Allow "outline" in export statements
            TokenKind::Common => "common",     // Allow "common" in paths (stdlib directory name)
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };
        self.advance();
        Ok(name.to_string())
    }

    /// Expect an identifier or a keyword that can be used as a method/field name.
    /// This allows using reserved words like 'new', 'type', etc. as method names.
    pub(crate) fn expect_method_name(&mut self) -> Result<String, ParseError> {
        // First try regular identifier
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }

        // Support f-strings and strings for macro template substitution
        // This allows: fn "get_{field}"() or fn "get_value"()
        match &self.current.kind {
            TokenKind::FString(_)
            | TokenKind::String(_)
            | TokenKind::RawString(_)
            | TokenKind::TypedString(_, _)
            | TokenKind::TypedRawString(_, _) => {
                let lexeme = self.current.lexeme.clone();
                self.advance();
                // Keep the string as-is (with quotes/template markers)
                // The macro expansion will handle template substitution
                return Ok(lexeme);
            }
            _ => {}
        }

        // Allow certain keywords as method names
        let name = match &self.current.kind {
            TokenKind::New => "new",
            TokenKind::Type => "type",
            TokenKind::Unit => "unit",
            TokenKind::Match => "match",
            TokenKind::Is => "is",
            TokenKind::As => "as",
            TokenKind::In => "in",
            TokenKind::Or => "or",
            TokenKind::And => "and",
            TokenKind::Not => "not",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::For => "for",
            TokenKind::While => "while",
            TokenKind::Loop => "loop",
            TokenKind::Return => "return",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::Result => "result",
            TokenKind::Out => "out",
            TokenKind::OutErr => "out_err",
            // Infix keywords can also be method names
            TokenKind::To => "to",
            TokenKind::NotTo => "not_to",
            // Allow 'with' as method name for SIMD v.with(idx, val)
            TokenKind::With => "with",
            // Allow 'default' as method name (e.g., Type::default())
            TokenKind::Default => "default",
            // Allow BDD/Gherkin keywords as method/field names
            TokenKind::Context => "context",
            TokenKind::Feature => "feature",
            TokenKind::Scenario => "scenario",
            TokenKind::Given => "given",
            TokenKind::When => "when",
            TokenKind::Then => "then",
            // Allow 'from' as method name (e.g., FilePath::from(path))
            TokenKind::From => "from",
            // Allow 'common' as method/field name (e.g., obj.common)
            TokenKind::Common => "common",
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };
        self.advance();
        Ok(name.to_string())
    }

    /// Check if a type should be treated as a borrow type
    /// Types ending with _borrow are borrow references
    pub(crate) fn is_borrow_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Simple(name) => name.ends_with("_borrow"),
            Type::Generic { name, .. } => name.ends_with("_borrow"),
            _ => false,
        }
    }

    /// Process a macro invocation's contract at parse time for LL(1) integration.
    ///
    /// This method:
    /// 1. Looks up the macro definition from the registry
    /// 2. Extracts const argument values from the invocation
    /// 3. Processes the contract to register introduced symbols
    ///
    /// Any errors are silently ignored (the interpreter will catch them later).
    pub(crate) fn process_macro_contract_ll1(&mut self, macro_name: &str, args: &[MacroArg]) {
        // Look up the macro definition
        let macro_def = match self.macro_registry.get_macro(macro_name) {
            Some(def) => def.clone(),
            None => return, // Unknown macro - will be caught later
        };

        // Extract const arguments
        let mut const_args: HashMap<String, ConstValue> = HashMap::new();

        for (idx, param) in macro_def.params.iter().enumerate() {
            if param.is_const {
                if let Some(MacroArg::Expr(expr)) = args.get(idx) {
                    // Try to evaluate the expression as a const value
                    if let Some(value) = self.try_eval_const_expr(expr) {
                        const_args.insert(param.name.clone(), value);
                    }
                }
            }
        }

        // Process the macro contract
        let scope = self.current_scope.clone();
        let _ = self
            .macro_registry
            .process_macro_invocation(macro_name, &const_args, &scope);
    }

    /// Try to evaluate an expression as a compile-time constant.
    /// Returns None if the expression cannot be evaluated at compile time.
    fn try_eval_const_expr(&self, expr: &Expr) -> Option<ConstValue> {
        match expr {
            Expr::Integer(n) => Some(ConstValue::Int(*n)),
            Expr::String(s) => Some(ConstValue::Str(s.clone())),
            Expr::Bool(b) => Some(ConstValue::Bool(*b)),
            Expr::Identifier(_name) => {
                // Could look up in a const environment if we had one
                None
            }
            Expr::Binary { left, op, right } => {
                let l = self.try_eval_const_expr(left)?;
                let r = self.try_eval_const_expr(right)?;
                self.eval_const_binary_op(&l, op, &r)
            }
            Expr::Unary { op, operand } => {
                let v = self.try_eval_const_expr(operand)?;
                self.eval_const_unary_op(op, &v)
            }
            _ => None,
        }
    }

    /// Evaluate a binary operation on const values
    fn eval_const_binary_op(
        &self,
        left: &ConstValue,
        op: &BinOp,
        right: &ConstValue,
    ) -> Option<ConstValue> {
        match (left, right) {
            (ConstValue::Int(l), ConstValue::Int(r)) => match op {
                BinOp::Add => Some(ConstValue::Int(l + r)),
                BinOp::Sub => Some(ConstValue::Int(l - r)),
                BinOp::Mul => Some(ConstValue::Int(l * r)),
                BinOp::Div if *r != 0 => Some(ConstValue::Int(l / r)),
                BinOp::Mod if *r != 0 => Some(ConstValue::Int(l % r)),
                BinOp::Eq => Some(ConstValue::Bool(l == r)),
                BinOp::NotEq => Some(ConstValue::Bool(l != r)),
                BinOp::Lt => Some(ConstValue::Bool(l < r)),
                BinOp::LtEq => Some(ConstValue::Bool(l <= r)),
                BinOp::Gt => Some(ConstValue::Bool(l > r)),
                BinOp::GtEq => Some(ConstValue::Bool(l >= r)),
                _ => None,
            },
            (ConstValue::Str(l), ConstValue::Str(r)) => match op {
                BinOp::Add => Some(ConstValue::Str(format!("{}{}", l, r))),
                BinOp::Eq => Some(ConstValue::Bool(l == r)),
                BinOp::NotEq => Some(ConstValue::Bool(l != r)),
                _ => None,
            },
            (ConstValue::Bool(l), ConstValue::Bool(r)) => match op {
                BinOp::And => Some(ConstValue::Bool(*l && *r)),
                BinOp::Or => Some(ConstValue::Bool(*l || *r)),
                BinOp::Eq => Some(ConstValue::Bool(l == r)),
                BinOp::NotEq => Some(ConstValue::Bool(l != r)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Evaluate a unary operation on a const value
    fn eval_const_unary_op(&self, op: &UnaryOp, value: &ConstValue) -> Option<ConstValue> {
        match (op, value) {
            (UnaryOp::Neg, ConstValue::Int(n)) => Some(ConstValue::Int(-n)),
            (UnaryOp::Not, ConstValue::Bool(b)) => Some(ConstValue::Bool(!b)),
            _ => None,
        }
    }

    /// Parse generic type parameters: <T, U, V> or [T, U, V] or [T, const N: usize]
    /// Both angle brackets and square brackets are supported for compatibility
    /// Returns empty Vec if no generic parameters are present
    pub(crate) fn parse_generic_params(&mut self) -> Result<Vec<GenericParam>, ParseError> {
        // Check for angle brackets <T> or square brackets [T]
        let use_brackets = if self.check(&TokenKind::Lt) {
            self.advance(); // consume '<'
            false
        } else if self.check(&TokenKind::LBracket) {
            // Emit deprecation warning for square bracket syntax
            use crate::error_recovery::{ErrorHint, ErrorHintLevel};
            let bracket_span = self.current.span;
            let warning = ErrorHint {
                level: ErrorHintLevel::Warning,
                message: "Deprecated syntax for generic parameters".to_string(),
                span: bracket_span,
                suggestion: Some("Use angle brackets <...> instead of [...]".to_string()),
                help: Some(
                    "Run `simple migrate --fix-generics` to automatically update your code"
                        .to_string(),
                ),
            };
            self.error_hints.push(warning);

            self.advance(); // consume '['
            true
        } else {
            return Ok(Vec::new());
        };

        let mut params = Vec::new();
        let end_token = if use_brackets {
            TokenKind::RBracket
        } else {
            TokenKind::Gt
        };

        while !self.check(&end_token) {
            // Check for const generic parameter: const N: usize
            if self.check(&TokenKind::Const) {
                self.advance(); // consume 'const'
                let name = self.expect_identifier()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                params.push(GenericParam::Const { name, ty });
            } else {
                let name = self.expect_identifier()?;

                // Check for trait bounds: T: Display or I: Iterator<Item=T>
                let mut bounds = Vec::new();
                if self.check(&TokenKind::Colon) {
                    self.advance(); // consume ':'

                    // Parse first bound as identifier (with optional generic args)
                    let bound_name = self.expect_identifier()?;

                    // Check for generic arguments in bound: Iterator<Item=T>
                    // Note: For now, we skip parsing the full generic args to avoid complexity
                    // and just store the trait name. Full support for associated type constraints
                    // like Item=T would require more AST changes.
                    if self.check(&TokenKind::Lt) {
                        // Skip generic arguments for now
                        let mut depth = 1;
                        self.advance(); // consume '<'
                        while depth > 0 && !self.is_at_end() {
                            if self.check(&TokenKind::Lt) {
                                depth += 1;
                                self.advance();
                            } else if self.check(&TokenKind::Gt) {
                                depth -= 1;
                                self.advance();
                            } else if self.check(&TokenKind::ShiftRight) {
                                // >> is two > tokens
                                if depth == 1 {
                                    // Special case: depth is 1, so first > closes inner generics
                                    // Second > belongs to outer context (function generic params)
                                    // Don't consume the >> token - just exit the loop
                                    break;
                                } else {
                                    depth -= 2;
                                    self.advance();
                                }
                            } else {
                                self.advance();
                            }
                        }
                    }

                    bounds.push(bound_name);

                    // Parse additional bounds with + separator: T: Display + Debug
                    while self.check(&TokenKind::Plus) {
                        self.advance(); // consume '+'
                        let bound_name = self.expect_identifier()?;

                        // Skip generic args for additional bounds too
                        if self.check(&TokenKind::Lt) {
                            let mut depth = 1;
                            self.advance();
                            while depth > 0 && !self.is_at_end() {
                                if self.check(&TokenKind::Lt) {
                                    depth += 1;
                                    self.advance();
                                } else if self.check(&TokenKind::Gt) {
                                    depth -= 1;
                                    self.advance();
                                } else if self.check(&TokenKind::ShiftRight) {
                                    if depth == 1 {
                                        // First > closes inner generics, second > belongs to outer context
                                        break;
                                    } else {
                                        depth -= 2;
                                        self.advance();
                                    }
                                } else {
                                    self.advance();
                                }
                            }
                        }

                        bounds.push(bound_name);
                    }
                }

                // Parse optional default type: Rhs = Self or T = i32
                let default = if self.check(&TokenKind::Assign) {
                    self.advance(); // consume '='
                    Some(self.parse_type()?)
                } else {
                    None
                };

                params.push(GenericParam::Type {
                    name,
                    bounds,
                    default,
                });
            }

            // Check for end of generic parameters or comma before next parameter
            // Special case: >> token when using angle brackets means we're at the end
            if !use_brackets && self.check(&TokenKind::ShiftRight) {
                // >> acts as the closing > for this generic param list
                // Don't consume it here - the loop will exit and handle it below
                break;
            }

            if !self.check(&end_token) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        if use_brackets {
            self.expect(&TokenKind::RBracket)?; // consume ']'
        } else {
            // Handle >> token splitting for nested generics
            if self.check(&TokenKind::ShiftRight) {
                // Split >> into two > tokens
                // This happens with nested generics like <I: Iterator<T>>
                // The first > closes our generic param list
                // The second > belongs to outer context
                use crate::token::{Span, Token};

                let shift_span = self.current.span.clone();

                // Create first > token (replaces current >>)
                let first_gt = Token::new(
                    TokenKind::Gt,
                    Span::new(
                        shift_span.start,
                        shift_span.start + 1,
                        shift_span.line,
                        shift_span.column,
                    ),
                    ">".to_string(),
                );

                // Create second > token (goes to pending)
                let second_gt = Token::new(
                    TokenKind::Gt,
                    Span::new(
                        shift_span.start + 1,
                        shift_span.end,
                        shift_span.line,
                        shift_span.column + 1,
                    ),
                    ">".to_string(),
                );

                // Replace current token with first >
                self.current = first_gt;
                // Push second > to pending
                self.pending_tokens.push_front(second_gt);

                // Now advance past the first > (moves to second >)
                self.advance();
                // And advance past the second > too (closes our generic param list)
                self.advance();
            } else {
                self.expect(&TokenKind::Gt)?; // consume '>'
            }
        }

        Ok(params)
    }

    /// Parse generic type parameters as strings (for backward compatibility)
    /// Ignores const parameters and trait bounds, returns only type parameter names
    pub(crate) fn parse_generic_params_as_strings(&mut self) -> Result<Vec<String>, ParseError> {
        let params = self.parse_generic_params()?;
        Ok(params
            .into_iter()
            .filter_map(|p| {
                match p {
                    GenericParam::Type { name, .. } => Some(name),
                    GenericParam::Const { .. } => None, // Skip const params for now
                }
            })
            .collect())
    }
}
