use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

mod collections;
mod control;
mod i18n;
mod identifiers;
mod lambdas;
mod literals;
mod math;

impl<'a> Parser<'a> {
    pub(crate) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            // Ellipsis as expression placeholder: `...` is equivalent to pass/unit ()
            // Used in specs and stubs: `fn foo(): ...`
            TokenKind::Ellipsis => {
                self.advance();
                Ok(Expr::Tuple(vec![]))
            }
            // Placeholder syntax: _ in expressions (for placeholder lambdas like nums.map(_ * 2))
            // The _ is parsed as an identifier and later transformed in argument parsing
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr::Identifier("_".to_string()))
            }
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
            | TokenKind::Atom(_)
            | TokenKind::CustomBlock { .. } => self.parse_primary_literal(),
            TokenKind::I18nString { .. } | TokenKind::I18nFString { .. } => self.parse_i18n_literal(),
            TokenKind::Result
            | TokenKind::Identifier { .. }
            | TokenKind::Self_
            | TokenKind::Super
            | TokenKind::Out
            | TokenKind::OutErr
            | TokenKind::Type
            | TokenKind::Feature
            | TokenKind::Scenario
            | TokenKind::Outline
            | TokenKind::Examples
            | TokenKind::Given
            | TokenKind::When
            | TokenKind::Then
            | TokenKind::AndThen
            | TokenKind::Context
            | TokenKind::Common
            | TokenKind::Vec
            | TokenKind::Gpu
            | TokenKind::Slice
            | TokenKind::Flat
            | TokenKind::Alias
            | TokenKind::Bounds
            | TokenKind::Default
            | TokenKind::From
            | TokenKind::To
            | TokenKind::Loop
            | TokenKind::Unit
            | TokenKind::Sync
            | TokenKind::Async
            | TokenKind::Kernel
            | TokenKind::Val
            | TokenKind::Literal
            | TokenKind::As
            | TokenKind::Repr
            | TokenKind::Extern
            | TokenKind::Static
            | TokenKind::Const
            | TokenKind::Shared
            | TokenKind::Dyn
            | TokenKind::Macro
            | TokenKind::Mixin
            | TokenKind::Actor
            | TokenKind::Ghost
            | TokenKind::Gen
            | TokenKind::Impl
            | TokenKind::Exists
            | TokenKind::Me
            | TokenKind::Asm
            | TokenKind::Bitfield
            | TokenKind::Newtype
            | TokenKind::Extend
            | TokenKind::Comptime
            | TokenKind::Struct
            | TokenKind::Enum
            | TokenKind::Class
            | TokenKind::Trait => self.parse_primary_identifier(),
            TokenKind::Backslash | TokenKind::Pipe | TokenKind::Move => self.parse_primary_lambda(),
            // fn(): lambda syntax (alias for \:) - only in expression context
            // Check if fn is IMMEDIATELY followed by ( (no identifier) to distinguish from function definitions
            // fn(): ... => lambda
            // fn name(): ... => function definition (not allowed in expression position)
            TokenKind::Fn => {
                // Peek at next token to see if it's immediately LParen
                let next = self.peek_next();

                // Only treat as lambda if IMMEDIATELY followed by (
                // This distinguishes fn(): from fn name():
                if matches!(next.kind, TokenKind::LParen) {
                    // Check that current and next tokens are adjacent (no whitespace/identifier between)
                    // In Simple, fn( is lambda, but fn foo( is function definition
                    self.parse_primary_lambda()
                } else {
                    return Err(ParseError::unexpected_token(
                        "expression",
                        "fn (function definitions are not expressions - use fn(): for lambdas)",
                        self.current.span,
                    ));
                }
            }
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => self.parse_primary_collection(),
            // Handle 'new' specially: if followed by a type (identifier, &, *, etc.), it's allocation
            // Otherwise, it's used as a variable name identifier
            TokenKind::New => {
                // Peek at next token
                let next = self.peek_next();

                // Check if next token indicates allocation context: new Type, new &Type, new *Type
                match next.kind {
                    TokenKind::Identifier { .. }
                    | TokenKind::Ampersand
                    | TokenKind::Star
                    | TokenKind::Plus
                    | TokenKind::Minus => {
                        // Allocation: new Type(...) or new &Type(...)
                        self.parse_primary_control()
                    }
                    _ => {
                        // Identifier: used as variable name like 'is_new or new'
                        self.parse_primary_identifier()
                    }
                }
            }
            // Handle 'old' specially: if followed by (, it's contract old(x)
            // Otherwise, it's used as a variable name identifier
            TokenKind::Old => {
                let next = self.peek_next();

                if matches!(next.kind, TokenKind::LParen) {
                    // Contract: old(x)
                    self.parse_primary_control()
                } else {
                    // Identifier: used as variable name
                    self.parse_primary_identifier()
                }
            }
            // `match` can be used as a variable name (e.g., `for match in matches: match.0`)
            // If followed by `.` or `=`, treat as identifier
            TokenKind::Match if self.peek_is(&TokenKind::Dot) || self.peek_is(&TokenKind::Assign) => self.parse_primary_identifier(),
            TokenKind::Spawn
            | TokenKind::Go
            | TokenKind::If
            | TokenKind::Elif
            | TokenKind::Match
            | TokenKind::Dollar => self.parse_primary_control(),
            TokenKind::Grid | TokenKind::Tensor => self.parse_primary_math(),
            TokenKind::At => {
                // FFI call prefix: @rt_function_name
                // No ambiguity: decorators only appear before declarations, not in expressions
                // Matrix multiplication (@) requires a left operand, while @rt_func appears at expression start

                // Peek at next token to see if it's an identifier
                let next = self.peek_next();

                if matches!(next.kind, TokenKind::Identifier { .. }) {
                    self.advance(); // consume '@'
                    let name = self.expect_identifier()?;
                    // Create identifier with @ prefix preserved for debugging/tooling
                    Ok(Expr::Identifier(format!("@{}", name)))
                } else {
                    // Not an FFI call pattern - let it fall through to default error
                    Err(ParseError::unexpected_token(
                        "expression",
                        format!(
                            "@ (matrix multiplication requires left operand, FFI calls require @identifier pattern)"
                        ),
                        self.current.span,
                    ))
                }
            }
            _ => Err(ParseError::unexpected_token(
                "expression",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
