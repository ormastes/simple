//! Simple language parser
//!
//! This module provides a recursive descent parser with Pratt parsing for expressions.
//! The parser is split into multiple submodules for maintainability:
//! - `expressions/` - Expression parsing (Pratt parser)
//! - `statements/` - Statement parsing (let, if, for, etc.)
//! - `types_def/` - Type definition parsing (struct, class, enum, etc.)
//! - `parser_types` - Type parsing methods
//! - `parser_patterns` - Pattern parsing methods

use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::Lexer;
use crate::token::{Span, Token, TokenKind};

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

pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) current: Token,
    pub(crate) previous: Token,
    #[allow(dead_code)]
    source: &'a str,
    pub(crate) pending_token: Option<Token>,
    /// Parser mode (Normal or Strict)
    pub(crate) mode: ParserMode,
    /// Depth of no-paren calls (for strict mode enforcement)
    pub(crate) no_paren_depth: u32,
    /// When true, pattern parser won't try typed pattern (name: Type)
    /// because colon is the match arm body delimiter
    pub(crate) in_match_arm_pattern: bool,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let previous = Token::new(TokenKind::Eof, Span::new(0, 0, 1, 1), String::new());

        Self {
            lexer,
            current,
            previous,
            source,
            pending_token: None,
            mode: ParserMode::Normal,
            no_paren_depth: 0,
            in_match_arm_pattern: false,
        }
    }

    /// Create a parser with a specific mode (Normal or Strict).
    /// Strict mode requires parentheses for inner function calls within no-paren call arguments.
    pub fn with_mode(source: &'a str, mode: ParserMode) -> Self {
        let mut parser = Self::new(source);
        parser.mode = mode;
        parser
    }

    pub fn parse(&mut self) -> Result<Module, ParseError> {
        let mut items = Vec::new();

        while !self.is_at_end() {
            // Skip newlines and stray dedents at top level
            // (Stray dedents can appear from multi-line expression continuations
            //  inside if/while conditions like `if a or\n   b:`)
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }

            // Skip stray RParen/RBracket/RBrace at top level
            // These can appear from partially-commented-out constructor calls
            if self.check(&TokenKind::RParen)
                || self.check(&TokenKind::RBrace)
            {
                self.advance();
                continue;
            }

            // Skip diff markers: lines starting with + or - at column 1
            // These appear in files with unresolved git conflicts
            if (self.check(&TokenKind::Plus) || self.check(&TokenKind::Minus))
                && self.current.span.column <= 1
            {
                // Skip the +/- prefix and continue parsing
                self.advance();
                continue;
            }

            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(_) => {
                    // Error recovery: skip to next line and continue parsing
                    while !self.check(&TokenKind::Newline)
                        && !self.check(&TokenKind::Eof)
                        && !self.is_at_end()
                    {
                        self.advance();
                    }
                    if self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
            }
        }

        Ok(Module { name: None, items })
    }

    pub(crate) fn parse_item(&mut self) -> Result<Node, ParseError> {
        // Skip leading newlines
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Skip // comments (C-style line comments used in some files)
        while self.check(&TokenKind::DoubleSlash) {
            // Skip to end of line
            while !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.is_at_end() {
                self.advance();
            }
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Check for doc comment before item
        let doc_comment = self.try_parse_doc_comment();

        // If a doc comment was consumed but nothing declaration-like follows,
        // treat the doc comment as a string literal expression (e.g., triple-quoted
        // strings used as return values inside function bodies).
        if let Some(ref dc) = doc_comment {
            if matches!(
                &self.current.kind,
                TokenKind::Dedent | TokenKind::Eof | TokenKind::RBrace
                    | TokenKind::RParen | TokenKind::RBracket
            ) {
                return Ok(Node::Expression(Expr::String(dc.content.clone())));
            }
        }

        // Skip `arch { ... }` blocks (SDN-like configuration blocks in __init__.spl files)
        if let TokenKind::Identifier(name) = &self.current.kind {
            if name == "arch" {
                // Peek to see if next token is LBrace
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::LBrace {
                    return self.skip_braced_block();
                }
            }
            // Handle `try: ... catch name: ...` — try/catch blocks
            if name == "try" {
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Colon {
                    return self.parse_try_catch();
                }
            }
            // Handle `bind Name = Type` — skip the binding statement
            if name == "bind" {
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(next.kind, TokenKind::Identifier(_)) {
                    self.advance(); // consume 'bind'
                    let _name = self.expect_identifier()?;
                    self.expect(&TokenKind::Assign)?;
                    let _value = self.parse_expression()?;
                    return Ok(Node::Expression(Expr::Nil));
                }
            }
        }

        match &self.current.kind {
            TokenKind::Hash => self.parse_attributed_item_with_doc(doc_comment),
            TokenKind::At => self.parse_decorated_function_with_doc(doc_comment),
            TokenKind::Fn => {
                // Disambiguate: `fn name(...)` is a function declaration,
                // but `fn(...)` (fn followed directly by LParen) is an expression (lambda or call)
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(next.kind, TokenKind::LParen) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_function_with_doc(doc_comment)
                }
            }
            TokenKind::Async => self.parse_async_function_with_doc(doc_comment),
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
            TokenKind::Mut => self.parse_mut_let(),
            TokenKind::Let => self.parse_let(),
            TokenKind::Var => self.parse_var(),
            TokenKind::Me => {
                // Check if this is a method definition or just an identifier
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // Accept Identifier or any keyword that could be a method name
                let is_method_name = matches!(&next.kind,
                    TokenKind::Identifier(_)
                    | TokenKind::Spawn | TokenKind::Move | TokenKind::Continue
                    | TokenKind::Break | TokenKind::Return | TokenKind::Match
                    | TokenKind::From | TokenKind::To | TokenKind::In | TokenKind::As
                    | TokenKind::Context | TokenKind::Type | TokenKind::Result
                    | TokenKind::Out | TokenKind::OutErr | TokenKind::Old
                    | TokenKind::Use | TokenKind::Import | TokenKind::Export
                    | TokenKind::New | TokenKind::Loop | TokenKind::For | TokenKind::While
                    | TokenKind::If | TokenKind::Else | TokenKind::Case
                    | TokenKind::Vec | TokenKind::Gpu | TokenKind::Dyn
                    | TokenKind::Shared | TokenKind::Common | TokenKind::Auto | TokenKind::With
                    | TokenKind::Mut | TokenKind::Pub | TokenKind::Priv
                    | TokenKind::Static | TokenKind::Const | TokenKind::Extern
                    | TokenKind::Fn | TokenKind::Async | TokenKind::Await | TokenKind::Yield
                );
                if is_method_name {
                    self.parse_me_method()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::PassDoNothing | TokenKind::PassDn | TokenKind::Pass => {
                self.advance();
                Ok(Node::Expression(Expr::Nil))
            }
            TokenKind::PassTodo => {
                self.advance();
                Ok(Node::Expression(Expr::Nil))
            }
            TokenKind::Bitfield => self.parse_bitfield(),
            TokenKind::Alias => {
                // Disambiguate: alias declaration vs alias as identifier (var name)
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(
                    next.kind,
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LBracket
                ) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_alias()
                }
            }
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => {
                // Disambiguate: `static fn ...` / `static val ...` vs `static()` or `static == x` as expression
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                match &next.kind {
                    // static fn/async/mut/identifier = static declaration
                    TokenKind::Fn | TokenKind::Async | TokenKind::Mut => self.parse_static(),
                    // static followed by operator/call/index = expression using 'static' as variable
                    TokenKind::LParen | TokenKind::Dot | TokenKind::LBracket
                    | TokenKind::Assign | TokenKind::Comma | TokenKind::Newline
                    | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace | TokenKind::Eof
                    | TokenKind::Eq | TokenKind::NotEq | TokenKind::Lt | TokenKind::Gt
                    | TokenKind::LtEq | TokenKind::GtEq
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                    | TokenKind::And | TokenKind::Or | TokenKind::Pipe
                    | TokenKind::Question | TokenKind::DoubleQuestion
                    | TokenKind::Semicolon | TokenKind::Colon => {
                        self.parse_expression_or_assignment()
                    }
                    _ => self.parse_static(),
                }
            }
            TokenKind::Type => {
                // Check if this is a type alias (type Name = ...) or expression (expect type to eq)
                // Simple heuristic: type alias names are PascalCase (start with uppercase)
                // Expression context uses lowercase like "expect type to eq"
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());

                // Check if next token is an uppercase identifier (type alias pattern)
                if let TokenKind::Identifier(name) = &next.kind {
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
            TokenKind::Unit => {
                // Disambiguate: `unit name(...)` is a unit declaration,
                // but `unit = expr` or `unit.field` is an expression (variable named 'unit')
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(next.kind, TokenKind::Identifier(_)) {
                    self.parse_unit()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Extern => self.parse_extern(),
            TokenKind::Macro => self.parse_macro_def(),
            // Module system (Features #104-111)
            TokenKind::Use => self.parse_use(),
            TokenKind::Import => self.parse_import(), // alias for use
            TokenKind::Mod => {
                // Disambiguate: `module name:` is a module declaration,
                // but `module.field` or `module = ...` is an expression
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // Module name can be an identifier or a keyword used as identifier
                let is_name_token = !matches!(next.kind,
                    TokenKind::Dot | TokenKind::Assign | TokenKind::LBracket
                    | TokenKind::LParen | TokenKind::Comma | TokenKind::Newline
                    | TokenKind::Eof | TokenKind::RParen | TokenKind::RBracket
                    | TokenKind::RBrace | TokenKind::Colon | TokenKind::Semicolon
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star
                    | TokenKind::Slash | TokenKind::Percent
                    | TokenKind::Lt | TokenKind::Gt | TokenKind::Eq | TokenKind::NotEq
                    | TokenKind::Pipe | TokenKind::Ampersand
                    | TokenKind::PlusAssign | TokenKind::MinusAssign
                    | TokenKind::StarAssign | TokenKind::SlashAssign
                );
                if is_name_token {
                    self.parse_mod(Visibility::Private, vec![])
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Common => {
                // Disambiguate: `common use ...` is a common use import,
                // but `common.push(...)` or `common = ...` is an expression
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(next.kind, TokenKind::Use) {
                    self.parse_common_use()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Export => self.parse_export_use(),
            TokenKind::From => {
                // Disambiguate: `from X import Y` vs `from` as identifier (variable name)
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                match &next.kind {
                    // If followed by operator/dot/bracket/etc., treat as identifier
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LParen | TokenKind::LBracket
                    | TokenKind::Comma | TokenKind::Newline | TokenKind::RBrace
                    | TokenKind::RParen | TokenKind::RBracket | TokenKind::Eof
                    | TokenKind::Eq | TokenKind::NotEq | TokenKind::Lt | TokenKind::Gt
                    | TokenKind::LtEq | TokenKind::GtEq
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                    | TokenKind::And | TokenKind::Or | TokenKind::Pipe
                    | TokenKind::Question | TokenKind::DoubleQuestion
                    | TokenKind::Semicolon | TokenKind::Colon => {
                        self.parse_expression_or_assignment()
                    }
                    _ => self.parse_from_import(),
                }
            }
            TokenKind::Auto => self.parse_auto_import(),
            TokenKind::If => self.parse_if(),
            TokenKind::Match => {
                // Disambiguate: match expression vs match as identifier (var name)
                // A match *statement* needs: `match <expression>:` followed by arms.
                // So `match` followed by something that can start an expression AND is
                // not a statement-ending or operator token means it's a match statement.
                // Otherwise treat `match` as a variable name/expression.
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // `match` as identifier when followed by non-expression-start tokens
                let is_identifier_context = matches!(next.kind,
                    // Assignment operators
                    TokenKind::Assign | TokenKind::PlusAssign | TokenKind::MinusAssign
                    | TokenKind::StarAssign | TokenKind::SlashAssign
                    // Member access / indexing
                    | TokenKind::Dot | TokenKind::LBracket
                    // Statement-ending tokens (bare `match` on a line = return value)
                    | TokenKind::Newline | TokenKind::Eof | TokenKind::Dedent
                    // Closing delimiters (match used as argument/value)
                    | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
                    // Separators
                    | TokenKind::Comma | TokenKind::Semicolon
                    // Comparison / arithmetic / logical operators (match used in expression)
                    | TokenKind::Eq | TokenKind::NotEq | TokenKind::Lt | TokenKind::Gt
                    | TokenKind::LtEq | TokenKind::GtEq
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                    | TokenKind::Percent | TokenKind::And | TokenKind::Or
                    | TokenKind::Pipe | TokenKind::Ampersand
                    | TokenKind::To | TokenKind::NotTo
                    | TokenKind::Question | TokenKind::As
                    | TokenKind::WalrusAssign
                );
                if is_identifier_context {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_match_stmt()
                }
            }
            TokenKind::For => self.parse_for(),
            TokenKind::While => self.parse_while(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => {
                // Disambiguate: break as statement vs break as identifier (var name)
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(
                    next.kind,
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LBracket
                ) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_break()
                }
            }
            TokenKind::Continue => {
                // Disambiguate: continue as statement vs continue as identifier (var name)
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(
                    next.kind,
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LBracket
                ) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_continue()
                }
            }
            TokenKind::Context => {
                // Disambiguate: context expr: body VS context as identifier
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // context keyword syntax: context <expr>: <body>
                // If followed by assign/dot/paren/comma/newline, treat as identifier
                match &next.kind {
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LParen
                    | TokenKind::LBracket // context[0] index access
                    | TokenKind::Comma | TokenKind::Newline | TokenKind::RBrace
                    | TokenKind::RParen | TokenKind::RBracket | TokenKind::Eof
                    // Binary operators indicate context is used as a variable
                    | TokenKind::Eq | TokenKind::NotEq | TokenKind::Lt | TokenKind::Gt
                    | TokenKind::LtEq | TokenKind::GtEq
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                    | TokenKind::And | TokenKind::Or | TokenKind::Pipe
                    | TokenKind::Question | TokenKind::DoubleQuestion
                    | TokenKind::Semicolon | TokenKind::Colon => {
                        self.parse_expression_or_assignment()
                    }
                    _ => self.parse_context(),
                }
            }
            TokenKind::With => self.parse_with(),
            _ => self.parse_expression_or_assignment(),
        }
    }

    /// Try to parse a doc comment if one is present.
    /// Returns None if no doc comment, Some(DocComment) if found.
    /// Merges consecutive doc comments into a single DocComment.
    fn try_parse_doc_comment(&mut self) -> Option<DocComment> {
        // Skip newlines before doc comment
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        let mut contents = Vec::new();

        // Collect all consecutive doc comments
        while let TokenKind::DocComment(content) = &self.current.kind {
            let content = content.clone();
            contents.push(content);
            self.advance();
            // Skip newlines between doc comments
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if contents.is_empty() {
            None
        } else {
            // Merge all doc comments with newlines
            Some(DocComment::new(contents.join("\n")))
        }
    }

    fn parse_pub_item_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function_with_doc(doc_comment)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function_with_doc(doc_comment)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct_with_doc(doc_comment)?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class_with_doc(doc_comment)?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum_with_doc(doc_comment)?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Union => {
                let mut node = self.parse_union_with_doc(doc_comment)?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait_with_doc(doc_comment)?;
                if let Node::Trait(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Me => {
                let mut node = self.parse_me_method()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                    f.doc_comment = doc_comment;
                }
                Ok(node)
            }
            _ => self.parse_pub_item(),
        }
    }

    fn parse_pub_item(&mut self) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct()?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class()?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum()?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Union => {
                let mut node = self.parse_union()?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait()?;
                if let Node::Trait(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Actor => {
                let mut node = self.parse_actor()?;
                if let Node::Actor(ref mut a) = node {
                    a.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Const => {
                let mut node = self.parse_const()?;
                if let Node::Const(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Static => {
                let mut node = self.parse_static()?;
                if let Node::Static(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Type => {
                let mut node = self.parse_type_alias()?;
                if let Node::TypeAlias(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Unit => {
                let mut node = self.parse_unit()?;
                if let Node::Unit(ref mut u) = node {
                    u.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Extern => {
                let mut node = self.parse_extern()?;
                if let Node::Extern(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Macro => {
                let mut node = self.parse_macro_def()?;
                if let Node::Macro(ref mut m) = node {
                    m.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Public, vec![]),
            TokenKind::Let => {
                self.parse_let()
            }
            TokenKind::Var => {
                self.parse_var()
            }
            TokenKind::Me => {
                let mut node = self.parse_me_method()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Alias => {
                let mut node = self.parse_alias()?;
                if let Node::TypeAlias(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Bitfield => {
                let mut node = self.parse_bitfield()?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Use => {
                // pub use X.Y.Z — public re-export (treat as export use)
                self.parse_export_use_from_pub()
            }
            TokenKind::Import => {
                // pub import X.Y — public import
                self.parse_use()
            }
            TokenKind::Identifier(_) => {
                // pub field_name: Type — public field declaration (inside class/struct)
                // or pub name = expr — public variable/binding
                self.parse_expression_or_assignment()
            }
            TokenKind::Export => {
                self.parse_export_use()
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, trait, actor, const, static, type, extern, macro, or mod after 'pub'",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Function Parsing ===

    pub(crate) fn parse_async_function(&mut self) -> Result<Node, ParseError> {
        self.advance(); // consume 'async'
        let mut func = self.parse_function()?;
        if let Node::Function(ref mut f) = func {
            f.effect = Some(Effect::Async);
        }
        Ok(func)
    }

    pub(crate) fn parse_function(&mut self) -> Result<Node, ParseError> {
        self.parse_function_with_decorators(vec![])
    }

    fn parse_function_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        self.parse_function_with_attrs(decorators, vec![])
    }

    fn parse_function_with_attrs(
        &mut self,
        decorators: Vec<Decorator>,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let mut name = self.expect_identifier()?;
        // Handle `fn name?()` or `fn name!()` - predicate/bang function names
        if self.check(&TokenKind::Question) {
            name.push('?');
            self.advance();
        } else if self.check(&TokenKind::Bang) {
            name.push('!');
            self.advance();
        }
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        // Handle multi-line function signatures where -> is on a continuation line:
        //   fn foo(params)
        //       -> ReturnType:
        //       body...
        let mut consumed_continuation_indent = false;
        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else if self.check(&TokenKind::Newline) {
            // Peek ahead: check if Newline -> Indent -> Arrow
            // Get tok1 non-destructively by ensuring it's in pending_token
            let _had_pending = self.pending_token.is_some();
            let tok1 = if let Some(ref pt) = self.pending_token {
                pt.clone()
            } else {
                let t = self.lexer.next_token();
                self.pending_token = Some(t.clone());
                t
            };
            let is_continuation = if tok1.kind == TokenKind::Indent {
                // Check the token after Indent - need to peek further
                let tok2 = self.lexer.next_token();
                let result = tok2.kind == TokenKind::Arrow;
                if result {
                    // Consume: Newline, Indent, Arrow
                    self.advance(); // consume Newline, current = Indent (from pending)
                    self.pending_token = Some(tok2); // set Arrow as pending
                    self.advance(); // consume Indent, current = Arrow
                    self.advance(); // consume Arrow, current = next token (e.g., type name)
                    consumed_continuation_indent = true;
                    true
                } else {
                    // Restore: tok1 stays in pending_token (already there)
                    // Push tok2 back to lexer
                    self.lexer.pending_tokens.push(tok2);
                    false
                }
            } else if tok1.kind == TokenKind::Arrow {
                // No Indent between Newline and Arrow (rare but possible)
                // tok1 is already in pending_token
                self.advance(); // consume Newline, current = Arrow (from pending)
                self.advance(); // consume Arrow, current = next token
                true
            } else {
                // Not a continuation, tok1 stays in pending_token
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

        // Parse optional where clause: where T: Clone + Default
        let where_clause = self.parse_where_clause()?;

        // Skip newlines before checking for contract blocks
        self.skip_newlines();

        // Parse optional contract block (new: in/out/out_err/invariant, legacy: requires/ensures)
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

        // Skip newlines after contract block before expecting colon
        self.skip_newlines();

        // Check for function body or abstract/forward declaration (no colon, no body)
        //
        // Disambiguate `fn name(): Type = expr` (colon as return type separator)
        // vs `fn name():` (colon as block start)
        let (body, is_abstract) = if self.check(&TokenKind::Colon) && return_type.is_none() {
            // When no return type was parsed via `->`  and we see `:`,
            // check if this is `fn name(): Type = expr`
            let saved_pos = self.current.span;
            let peeked = self.pending_token.clone()
                .unwrap_or_else(|| self.lexer.next_token());
            self.pending_token = Some(peeked.clone());
            let is_return_type_colon = if let TokenKind::Identifier(ref _name) = peeked.kind {
                let tok2 = self.lexer.next_token();
                let result = tok2.kind == TokenKind::Assign;
                self.lexer.pending_tokens.push(tok2);
                result
            } else {
                false
            };

            if is_return_type_colon {
                // Parse as `fn name(): RetType = expr`
                self.advance(); // consume ':'
                let _ret_ty = self.parse_type()?;
                self.expect(&TokenKind::Assign)?;
                let expr = self.parse_expression()?;
                (Block {
                    span: saved_pos,
                    statements: vec![Node::Return(crate::ast::ReturnStmt {
                        span: saved_pos,
                        value: Some(expr),
                    })],
                }, false)
            } else {
                // Regular colon block start - fall through to normal handling
                self.advance(); // consume ':'
                if consumed_continuation_indent {
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
                    (Block {
                        span: Span::new(block_span.start, self.previous.span.end, block_span.line, block_span.column),
                        statements: stmts,
                    }, false)
                } else {
                    (self.parse_block_or_inline()?, false)
                }
            }
        } else if self.check(&TokenKind::Colon) {
            // Colon with return type already parsed (e.g., `fn name() -> Type:`)
            self.advance();
            if consumed_continuation_indent {
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
                (Block {
                    span: Span::new(block_span.start, self.previous.span.end, block_span.line, block_span.column),
                    statements: stmts,
                }, false)
            } else {
                (self.parse_block_or_inline()?, false)
            }
        } else if self.check(&TokenKind::Newline) || self.check(&TokenKind::Eof) || self.check(&TokenKind::Dedent)
            // If the next token starts a new item, this function has no body (forward declaration)
            || self.check(&TokenKind::Fn) || self.check(&TokenKind::Struct) || self.check(&TokenKind::Class)
            || self.check(&TokenKind::Enum) || self.check(&TokenKind::Trait) || self.check(&TokenKind::Mixin) || self.check(&TokenKind::Impl)
            || self.check(&TokenKind::Pub) || self.check(&TokenKind::Hash) || self.check(&TokenKind::At)
            || self.check(&TokenKind::Export) || self.check(&TokenKind::Import) || self.check(&TokenKind::Use)
            || self.check(&TokenKind::Extern) || self.check(&TokenKind::Async)
            || self.check(&TokenKind::Var) || self.check(&TokenKind::Let)
            || self.check(&TokenKind::Me) || self.check(&TokenKind::Static)
        {
            // Forward declaration / abstract method: no body
            (Block {
                span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                statements: vec![],
            }, true)
        } else if self.check(&TokenKind::LBrace) {
            // Allow `{` as block delimiter (C/Rust style)
            (self.parse_braced_block()?, false)
        } else {
            self.expect(&TokenKind::Colon)?;
            (self.parse_block_or_inline()?, false)
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
            decorators,
            attributes,
            doc_comment: None,
            contract,
            is_abstract,
        }))
    }

    /// Parse optional where clause: `where T: Trait1 + Trait2, U: Other`
    pub(crate) fn parse_where_clause(&mut self) -> Result<WhereClause, ParseError> {
        if !self.check(&TokenKind::Where) {
            return Ok(vec![]);
        }

        self.advance(); // consume 'where'
        let mut bounds = Vec::new();

        loop {
            let span = self.current.span;
            let type_param = self.expect_identifier()?;

            // Accept both `:` (trait bounds) and `=` (type equality constraint)
            let mut trait_bounds = Vec::new();
            if self.check(&TokenKind::Assign) {
                // Type equality constraint: where T = Type
                self.advance(); // consume '='
                // Parse the type as a string by consuming tokens until comma/colon/newline
                let _type_val = self.parse_type()?;
                trait_bounds.push("=".to_string());
            } else {
                self.expect(&TokenKind::Colon)?;

                // Parse trait bounds: Trait1 + Trait2 + ...
                loop {
                    let bound_name = self.expect_identifier()?;
                    // Skip optional generic arguments on the bound: Add[Output=T] or Add<T>
                    let _ = self.parse_generic_params();
                    trait_bounds.push(bound_name);

                    // Check for + to continue parsing bounds
                    if self.check(&TokenKind::Plus) {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }

            bounds.push(WhereBound {
                span,
                type_param,
                bounds: trait_bounds,
            });

            // Check for comma to continue parsing more bounds
            if self.check(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }

        Ok(bounds)
    }

    // === Doc Comment Variants ===

    fn parse_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_async_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_async_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_decorated_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_decorated_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_struct_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_struct()?;
        if let Node::Struct(ref mut s) = node {
            s.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_class_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_class()?;
        if let Node::Class(ref mut c) = node {
            c.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_enum_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_enum()?;
        if let Node::Enum(ref mut e) = node {
            e.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_union_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_union()?;
        if let Node::Enum(ref mut e) = node {
            e.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_trait_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_trait()?;
        if let Node::Trait(ref mut t) = node {
            t.doc_comment = doc_comment;
        }
        Ok(node)
    }

    fn parse_attributed_item_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_attributed_item()?;
        // Set doc_comment on the parsed item
        match &mut node {
            Node::Function(f) => f.doc_comment = doc_comment,
            Node::Struct(s) => s.doc_comment = doc_comment,
            Node::Class(c) => c.doc_comment = doc_comment,
            Node::Enum(e) => e.doc_comment = doc_comment,
            Node::Trait(t) => t.doc_comment = doc_comment,
            _ => {}
        }
        Ok(node)
    }

    /// Parse an attributed item: #[attr] fn/struct/class/etc
    fn parse_attributed_item(&mut self) -> Result<Node, ParseError> {
        let mut attributes = Vec::new();

        // Parse all attributes (can be multiple: #[a] #[b] fn foo)
        while self.check(&TokenKind::Hash) {
            attributes.push(self.parse_attribute()?);
            // Skip newlines between attributes
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the item with collected attributes
        // Could be function, struct, class, etc.
        match &self.current.kind {
            TokenKind::At => {
                // Attributes followed by decorators
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    decorators.push(self.parse_decorator()?);
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
                self.parse_function_with_attrs(decorators, attributes)
            }
            TokenKind::Fn => self.parse_function_with_attrs(vec![], attributes),
            TokenKind::Async => {
                self.advance();
                let mut func = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = func {
                    f.effect = Some(Effect::Async);
                }
                Ok(func)
            }
            TokenKind::Struct => self.parse_struct_with_attrs(attributes),
            TokenKind::Class => self.parse_class_with_attrs(attributes),
            TokenKind::Enum => self.parse_enum_with_attrs(attributes),
            TokenKind::Union => self.parse_union_with_attrs(attributes),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_attrs(attributes)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Private, attributes),
            TokenKind::Trait => self.parse_trait(),
            TokenKind::Mixin => self.parse_mixin(),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Extern => self.parse_extern(),
            TokenKind::Use => self.parse_use(),
            TokenKind::Import => self.parse_import(),
            TokenKind::Export => self.parse_export_use(),
            TokenKind::From => self.parse_from_import(),
            TokenKind::Let => self.parse_let(),
            TokenKind::Var => self.parse_var(),
            // If there's a Dedent or Newline after attributes, treat as standalone attributes (no-op)
            TokenKind::Dedent | TokenKind::Newline | TokenKind::Eof => {
                Ok(Node::Expression(Expr::Nil))
            }
            _ => {
                // Try parsing as an expression or assignment (attributes on expressions)
                self.parse_expression_or_assignment()
            }
        }
    }

    /// Parse optional parenthesized argument list: `(arg1, arg2, ...)`
    /// Supports both positional and named arguments: `(name: value, other)`
    fn parse_optional_paren_args(&mut self) -> Result<Option<Vec<Expr>>, ParseError> {
        if self.check(&TokenKind::LParen) {
            self.advance();
            // Skip whitespace after opening paren
            self.skip_whitespace_tokens();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) && !self.is_at_end() {
                let expr = self.parse_expression()?;
                // Handle named arguments: name: value or name = value
                if self.check(&TokenKind::Colon) || self.check(&TokenKind::Assign) {
                    self.advance(); // consume ':' or '='
                    let _value = self.parse_expression()?;
                    // Store just the value for now (name is in `expr`)
                    args.push(_value);
                } else {
                    args.push(expr);
                }
                // Skip whitespace after argument
                self.skip_whitespace_tokens();
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                    self.skip_whitespace_tokens();
                }
            }
            self.expect(&TokenKind::RParen)?;
            Ok(Some(args))
        } else {
            Ok(None)
        }
    }

    /// Parse parenthesized type list: `(Type1, Type2, ...)`
    pub(crate) fn parse_paren_type_list(&mut self) -> Result<Vec<Type>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        // Skip whitespace after opening paren (for multi-line type lists)
        self.skip_whitespace_tokens();
        let mut types = Vec::new();
        while !self.check(&TokenKind::RParen) {
            // Handle named tuple type fields: (name: Type, ...)
            // Also handle `returns name: Type` prefix in macro return types
            if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "returns") {
                self.advance(); // consume 'returns'
            }
            let ty = self.parse_type()?;
            // If followed by colon, the parsed "type" was actually a field name
            if self.check(&TokenKind::Colon) {
                self.advance(); // consume ':'
                let actual_ty = self.parse_type()?;
                types.push(actual_ty);
            } else {
                types.push(ty);
            }
            // Skip whitespace after type
            self.skip_whitespace_tokens();
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
                // Skip whitespace after comma
                self.skip_whitespace_tokens();
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(types)
    }

    /// Parse a single attribute: #[name] or #[name = value] or #[name(args)]
    fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Hash)?;
        self.expect(&TokenKind::LBracket)?;

        // Parse the attribute name
        let name = self.expect_identifier()?;

        // Check for value: #[name = value]
        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // Check for arguments: #[name(arg1, arg2)]
        let args = self.parse_optional_paren_args()?;

        self.expect(&TokenKind::RBracket)?;

        Ok(Attribute {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            value,
            args,
        })
    }

    fn parse_pub_item_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct_with_attrs(attributes)?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class_with_attrs(attributes)?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Public, attributes),
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, or mod after pub with attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse a decorated function: @decorator fn foo(): ...
    fn parse_decorated_function(&mut self) -> Result<Node, ParseError> {
        let mut decorators = Vec::new();

        // Parse all decorators (can be multiple: @a @b fn foo)
        while self.check(&TokenKind::At) {
            decorators.push(self.parse_decorator()?);
            // Skip newlines between decorators
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the item with the collected decorators
        if self.check(&TokenKind::Fn) || self.check(&TokenKind::Async) {
            self.parse_function_with_decorators(decorators)
        } else if self.check(&TokenKind::Struct) || self.check(&TokenKind::Class)
            || self.check(&TokenKind::Enum) || self.check(&TokenKind::Union)
            || self.check(&TokenKind::Pub) || self.check(&TokenKind::Priv)
            || self.check(&TokenKind::Trait) || self.check(&TokenKind::Mixin) || self.check(&TokenKind::Impl)
            || self.check(&TokenKind::Extern) || self.check(&TokenKind::Me)
            || self.check(&TokenKind::Static)
        {
            // For non-function items (export, struct, class, etc.),
            // discard the decorators and parse as a regular item
            self.parse_item()
        } else {
            // No function or definition keyword follows — treat as expression statement.
            // This handles cases like `@function` or `@line` used as standalone expressions.
            if decorators.len() == 1 && decorators[0].args.is_none() {
                // Convert single no-arg decorator back to an expression: @name -> Identifier("@name")
                let expr = match &decorators[0].name {
                    Expr::Identifier(name) => Expr::Identifier(format!("@{}", name)),
                    other => other.clone(),
                };
                // Check for no-paren call arguments or assignment
                Ok(Node::Expression(expr))
            } else {
                // Multiple decorators or decorator with args — can't easily convert back
                // Fall through to regular item parsing
                self.parse_item()
            }
        }
    }

    /// Parse a single decorator: @name or @name(args)
    fn parse_decorator(&mut self) -> Result<Decorator, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Parse the decorator name (can be dotted: @module.decorator)
        let name = self.parse_primary()?;

        // Check for arguments: @decorator(arg1, arg2)
        let args = self.parse_optional_paren_args()?;

        Ok(Decorator {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            args,
        })
    }

    pub(crate) fn parse_parameters(&mut self) -> Result<Vec<Parameter>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();

        // Skip whitespace after opening paren (for multi-line parameter lists)
        self.skip_whitespace_tokens();

        while !self.check(&TokenKind::RParen) {
            let param_span = self.current.span;
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

            // Skip variadic indicator `...` after type (e.g., `items: T...`)
            if self.check(&TokenKind::Ellipsis) {
                self.advance();
            }

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
            });

            // Skip whitespace after parameter (for multi-line parameter lists)
            self.skip_whitespace_tokens();

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
                // Skip whitespace after comma (for multi-line parameter lists)
                self.skip_whitespace_tokens();
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    /// Parse a block that starts after a newline has already been consumed
    /// (used in match arms where colon+newline precede the indent)
    pub(crate) fn parse_block_after_newline(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;
        if !self.check(&TokenKind::Indent) {
            // Inside brackets: temporarily reset bracket_depth for proper INDENT/DEDENT
            if self.is_inside_brackets() {
                let saved_depth = self.lexer.bracket_depth;
                self.lexer.bracket_depth = 0;
                if let Some(stale) = self.pending_token.take() {
                    self.lexer.pending_tokens.push(stale);
                    self.lexer.at_line_start = true;
                }
                let result = if self.check(&TokenKind::Indent) {
                    self.expect(&TokenKind::Indent)?;
                    let mut statements = Vec::new();
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) || self.is_at_end() {
                            break;
                        }
                        statements.push(self.parse_item()?);
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                    Ok(Block {
                        span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                        statements,
                    })
                } else {
                    // No indent — parse items until block terminator
                    let mut statements = Vec::new();
                    while !self.is_at_end()
                        && !self.check(&TokenKind::RParen)
                        && !self.check(&TokenKind::RBrace)
                        && !self.check(&TokenKind::RBracket)
                        && !self.check(&TokenKind::Dedent)
                        && !self.check(&TokenKind::Elif)
                        && !self.check(&TokenKind::Else)
                        && !self.check(&TokenKind::Case)
                    {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.is_at_end()
                            || self.check(&TokenKind::RParen)
                            || self.check(&TokenKind::RBrace)
                            || self.check(&TokenKind::RBracket)
                            || self.check(&TokenKind::Dedent)
                            || self.check(&TokenKind::Elif)
                            || self.check(&TokenKind::Else)
                            || self.check(&TokenKind::Case)
                        {
                            break;
                        }
                        statements.push(self.parse_item()?);
                        if self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    Ok(Block {
                        span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                        statements,
                    })
                };
                self.lexer.bracket_depth = saved_depth;
                return result;
            }
            // Empty block — no indent after newline
            return Ok(Block {
                span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                statements: vec![],
            });
        }
        self.expect(&TokenKind::Indent)?;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            statements.push(self.parse_item()?);

            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

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

    /// Parse a braced block: `{ stmt; stmt; ... }`
    /// Used as alternative to `:` block delimiter (C/Rust style)
    pub(crate) fn parse_braced_block(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        self.skip_whitespace_tokens();
        while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
            self.skip_whitespace_tokens();
            if self.check(&TokenKind::RBrace) {
                break;
            }
            stmts.push(self.parse_item()?);
            self.skip_whitespace_tokens();
            // Skip optional semicolons between statements
            while self.check(&TokenKind::Semicolon) {
                self.advance();
                self.skip_whitespace_tokens();
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Block {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            statements: stmts,
        })
    }

    /// Parse a block that can be either:
    /// - Inline: `if cond: return val` (single statement on same line)
    /// - Indented: `if cond:\n    body` (newline + indent)
    /// - Empty: `if cond:\n` followed by next statement at same/lower indent
    pub(crate) fn parse_block_or_inline(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;

        // If no newline, parse a single inline statement
        if !self.check(&TokenKind::Newline) {
            let stmt = self.parse_item()?;
            return Ok(Block {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                statements: vec![stmt],
            });
        }

        self.expect(&TokenKind::Newline)?;

        // Handle inside-brackets case: no Indent/Dedent tokens available.
        // When inside brackets (parens/braces), the lexer suppresses INDENT/DEDENT.
        // For nested blocks (for/if/while bodies inside lambdas), we need to:
        // 1. Temporarily set bracket_depth=0 so the lexer emits INDENT/DEDENT
        // 2. Inject a synthetic INDENT token for the current indentation level
        // 3. Set up indent_stack so subsequent indentation changes produce correct tokens
        // 4. Parse the block normally
        // 5. Restore lexer state
        if !self.check(&TokenKind::Indent) && self.is_inside_brackets() {
            let saved_depth = self.lexer.bracket_depth;
            let saved_indent_stack = self.lexer.indent_stack.clone();
            self.lexer.bracket_depth = 0;

            // The current token was fetched with bracket_depth > 0, so indentation
            // was skipped. Its column tells us the indent level of the block body.
            let block_indent = (self.current.span.column as usize).saturating_sub(1);
            // Set up indent_stack: the top should be less than block_indent so that
            // subsequent lines at this level don't produce unwanted INDENT/DEDENT.
            // We use block_indent as the new top, meaning same-level lines are "at level"
            // and deeper lines produce INDENT.
            self.lexer.indent_stack = vec![0];
            // Push a level just below block_indent as the "base" for this block
            if block_indent > 0 {
                self.lexer.indent_stack.push(block_indent);
            }

            // Save the current token (first real token of the block body) as pending,
            // so it's returned AFTER we consume the synthetic INDENT.
            let stale_current = self.current.clone();
            if let Some(pending) = self.pending_token.take() {
                // Push further pending tokens to lexer so they come after stale_current
                self.lexer.pending_tokens.push(pending);
            }
            self.pending_token = Some(stale_current);

            // Inject synthetic INDENT as self.current
            self.current = Token::new(
                TokenKind::Indent,
                Span::new(
                    self.previous.span.end,
                    self.previous.span.end,
                    self.previous.span.line,
                    1,
                ),
                String::new(),
            );

            // Now self.current is INDENT — parse the block normally
            self.expect(&TokenKind::Indent)?;
            let mut statements = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end()
                && !self.check(&TokenKind::RParen)
                && !self.check(&TokenKind::RBracket)
                && !self.check(&TokenKind::RBrace)
            {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) || self.is_at_end()
                    || self.check(&TokenKind::RParen)
                    || self.check(&TokenKind::RBracket)
                    || self.check(&TokenKind::RBrace)
                {
                    break;
                }
                statements.push(self.parse_item()?);
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
            // Consume any extra DEDENTs from indent_stack cleanup
            while self.check(&TokenKind::Dedent) {
                self.advance();
            }
            if statements.is_empty() {
                statements.push(Node::Expression(Expr::Nil));
            }

            // Restore lexer state, accounting for bracket changes during temp period.
            // During temp, bracket_depth started at 0. Any closing brackets that
            // underflowed (saturating_sub from 0) represent brackets that should
            // decrement the restored depth. If self.current is a closing bracket
            // and bracket_depth is 0, one decrement was lost.
            let temp_depth = self.lexer.bracket_depth;
            if temp_depth == 0 && matches!(self.current.kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                // The closing bracket decremented from 0 to 0 — apply to saved
                self.lexer.bracket_depth = saved_depth.saturating_sub(1);
            } else {
                // No underflow: just add temp changes to saved
                self.lexer.bracket_depth = saved_depth + temp_depth;
            }
            self.lexer.indent_stack = saved_indent_stack;
            return Ok(Block {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                statements,
            });
        }

        // Handle empty block (newline but no indent) — treat as pass_do_nothing
        if !self.check(&TokenKind::Indent) {
            return Ok(Block {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                statements: vec![Node::Expression(Expr::Nil)],
            });
        }

        self.expect(&TokenKind::Indent)?;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            statements.push(self.parse_item()?);

            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

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

    pub(crate) fn parse_block(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;

        // Expect NEWLINE then INDENT
        self.expect(&TokenKind::Newline)?;
        if !self.check(&TokenKind::Indent) {
            // Inside brackets: inject synthetic INDENT and temporarily reset bracket_depth
            if self.is_inside_brackets() {
                let saved_depth = self.lexer.bracket_depth;
                let saved_indent_stack = self.lexer.indent_stack.clone();
                self.lexer.bracket_depth = 0;

                let block_indent = (self.current.span.column as usize).saturating_sub(1);
                self.lexer.indent_stack = vec![0];
                if block_indent > 0 {
                    self.lexer.indent_stack.push(block_indent);
                }

                // Save current token as pending (comes after synthetic INDENT)
                let stale_current = self.current.clone();
                if let Some(pending) = self.pending_token.take() {
                    self.lexer.pending_tokens.push(pending);
                }
                self.pending_token = Some(stale_current);

                // Inject synthetic INDENT
                self.current = Token::new(
                    TokenKind::Indent,
                    Span::new(
                        self.previous.span.end,
                        self.previous.span.end,
                        self.previous.span.line,
                        1,
                    ),
                    String::new(),
                );

                self.expect(&TokenKind::Indent)?;
                let mut statements = Vec::new();
                while !self.check(&TokenKind::Dedent) && !self.is_at_end()
                    && !self.check(&TokenKind::RParen)
                    && !self.check(&TokenKind::RBracket)
                    && !self.check(&TokenKind::RBrace)
                {
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    if self.check(&TokenKind::Dedent) || self.is_at_end()
                        || self.check(&TokenKind::RParen)
                        || self.check(&TokenKind::RBracket)
                        || self.check(&TokenKind::RBrace)
                    {
                        break;
                    }
                    match self.parse_item() {
                        Ok(item) => statements.push(item),
                        Err(_) => {
                            // Error recovery: skip to next line
                            while !self.check(&TokenKind::Newline)
                                && !self.check(&TokenKind::Dedent)
                                && !self.check(&TokenKind::Eof)
                                && !self.is_at_end()
                                && !self.check(&TokenKind::RParen)
                                && !self.check(&TokenKind::RBracket)
                                && !self.check(&TokenKind::RBrace)
                            {
                                self.advance();
                            }
                        }
                    }
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }
                while self.check(&TokenKind::Dedent) {
                    self.advance();
                }

                // Restore bracket_depth accounting for bracket changes during temp
                let temp_depth = self.lexer.bracket_depth;
                if temp_depth == 0 && matches!(self.current.kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                    self.lexer.bracket_depth = saved_depth.saturating_sub(1);
                } else {
                    self.lexer.bracket_depth = saved_depth + temp_depth;
                }
                self.lexer.indent_stack = saved_indent_stack;
                return Ok(Block {
                    span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                    statements,
                });
            }
            // Empty block — no indent after newline
            return Ok(Block {
                span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                statements: vec![],
            });
        }
        self.expect(&TokenKind::Indent)?;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            // Skip stray RParen/RBrace inside blocks (from partially-commented-out constructors)
            if self.check(&TokenKind::RParen) || self.check(&TokenKind::RBrace) {
                self.advance();
                continue;
            }

            // Skip diff markers: + or - at the start of a line inside blocks
            if (self.check(&TokenKind::Plus) || self.check(&TokenKind::Minus))
                && self.current.span.column <= 1
            {
                self.advance();
                continue;
            }

            match self.parse_item() {
                Ok(item) => statements.push(item),
                Err(_) => {
                    // Error recovery: skip to next line and continue parsing
                    while !self.check(&TokenKind::Newline)
                        && !self.check(&TokenKind::Dedent)
                        && !self.check(&TokenKind::Eof)
                        && !self.is_at_end()
                    {
                        self.advance();
                    }
                    if self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
            }

            // Consume newline after statement if present
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

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

    // === Helper Methods ===

    /// Skip a braced block like `arch { ... }` by consuming balanced braces.
    /// Returns a Nil expression as a placeholder.
    fn skip_braced_block(&mut self) -> Result<Node, ParseError> {
        self.advance(); // consume 'arch' (or whatever identifier)
        self.expect(&TokenKind::LBrace)?;
        let mut depth = 1u32;
        while depth > 0 && !self.is_at_end() {
            if self.check(&TokenKind::LBrace) {
                depth += 1;
            } else if self.check(&TokenKind::RBrace) {
                depth -= 1;
                if depth == 0 {
                    self.advance(); // consume the final '}'
                    break;
                }
            }
            self.advance();
        }
        Ok(Node::Expression(Expr::Nil))
    }

    pub(crate) fn advance(&mut self) {
        self.previous = std::mem::replace(
            &mut self.current,
            self.pending_token
                .take()
                .unwrap_or_else(|| self.lexer.next_token()),
        );
    }

    pub(crate) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current.kind) == std::mem::discriminant(kind)
    }

    pub(crate) fn is_at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    /// Check if the parser is inside brackets/parens/braces (no Indent/Dedent emitted)
    pub(crate) fn is_inside_brackets(&self) -> bool {
        self.lexer.bracket_depth > 0
    }

    /// Check if, after a Newline (and optional Indent), the given token kind appears.
    /// Used for multi-line `and`/`or` continuation without parentheses.
    /// Does NOT consume any tokens — returns false if current is not Newline.
    pub(crate) fn peek_past_newline_for(&mut self, kind: &TokenKind) -> bool {
        if !self.check(&TokenKind::Newline) {
            return false;
        }
        // Save state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_token.clone();

        // Peek past Newline and any Indent
        self.advance(); // consume Newline
        let first_from_pending = saved_pending.is_some();
        let mut lexer_tokens = Vec::new();
        if !first_from_pending {
            lexer_tokens.push(self.current.clone());
        }
        while self.check(&TokenKind::Indent) || self.check(&TokenKind::Newline) {
            self.advance();
            lexer_tokens.push(self.current.clone());
        }
        let found = self.check(kind);

        // Restore state
        let leftover_pending = self.pending_token.take();
        if let Some(lp) = leftover_pending {
            self.lexer.pending_tokens.push(lp);
        }
        for tok in lexer_tokens.into_iter().rev() {
            self.lexer.pending_tokens.push(tok);
        }
        self.current = saved_current;
        self.previous = saved_previous;
        self.pending_token = saved_pending;
        found
    }

    /// Peek at the next token without consuming current
    pub(crate) fn peek_is(&mut self, kind: &TokenKind) -> bool {
        // Save current state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        // Advance to peek
        self.advance();
        let result = self.check(kind);

        // Restore state
        self.pending_token = Some(self.current.clone());
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
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            Ok(name)
        } else if let TokenKind::Integer(n) = &self.current.kind {
            // Allow integer literals as identifiers in some contexts (e.g., module paths like 70.backend)
            let name = n.to_string();
            self.advance();
            Ok(name)
        } else {
            // Allow certain Simple keywords as identifiers (e.g., gpu as enum variant name)
            let name = match &self.current.kind {
                TokenKind::Nil => "nil",
                TokenKind::Gpu => "gpu",
                TokenKind::Me => "me",
                TokenKind::Var => "var",
                TokenKind::Alias => "alias",
                TokenKind::Bitfield => "bitfield",
                TokenKind::Pass => "pass",
                TokenKind::PassDoNothing => "pass_do_nothing",
                TokenKind::PassDn => "pass_dn",
                TokenKind::PassTodo => "pass_todo",
                TokenKind::Result => "result",
                TokenKind::Vec => "vec",
                TokenKind::Shared => "shared",
                TokenKind::Context => "context",
                TokenKind::To => "to",
                TokenKind::NotTo => "not_to",
                TokenKind::Spawn => "spawn",
                TokenKind::Move => "move",
                TokenKind::Dyn => "dyn",
                TokenKind::From => "from",
                TokenKind::Union => "union",
                TokenKind::Actor => "actor",
                TokenKind::Fn => "fn",
                TokenKind::Let => "let",
                TokenKind::Macro => "macro",
                TokenKind::With => "with",
                TokenKind::New => "new",
                TokenKind::Self_ => "self",
                TokenKind::Super => "super",
                TokenKind::Common => "common",
                TokenKind::Export => "export",
                TokenKind::Import => "import",
                TokenKind::Extern => "extern",
                TokenKind::Static => "static",
                TokenKind::Const => "const",
                TokenKind::Impl => "impl",
                TokenKind::Trait => "trait",
                TokenKind::Mixin => "mixin",
                TokenKind::Struct => "struct",
                TokenKind::Class => "class",
                TokenKind::Enum => "enum",
                TokenKind::Bool(true) | TokenKind::True => "true",
                TokenKind::Bool(false) | TokenKind::False => "false",
                TokenKind::Pub => "pub",
                TokenKind::Priv => "priv",
                TokenKind::Async => "async",
                TokenKind::Await => "await",
                TokenKind::Yield => "yield",
                TokenKind::Type => "type",
                TokenKind::Unit => "unit",
                TokenKind::Mod => "mod",
                TokenKind::Use => "use",
                TokenKind::Loop => "loop",
                TokenKind::For => "for",
                TokenKind::While => "while",
                TokenKind::If => "if",
                TokenKind::Else => "else",
                TokenKind::Match => "match",
                TokenKind::Return => "return",
                TokenKind::Break => "break",
                TokenKind::Continue => "continue",
                TokenKind::In => "in",
                TokenKind::Is => "is",
                TokenKind::As => "as",
                TokenKind::Or => "or",
                TokenKind::And => "and",
                TokenKind::Not => "not",
                TokenKind::Case => "case",
                TokenKind::Out => "out",
                TokenKind::OutErr => "out_err",
                TokenKind::Old => "old",
                TokenKind::Mut => "mut",
                TokenKind::Def => "def",
                TokenKind::WalrusAssign => "walrus_assign",
                TokenKind::Where => "where",
                TokenKind::Crate => "crate",
                TokenKind::Auto => "auto",
                TokenKind::Requires => "requires",
                TokenKind::Ensures => "ensures",
                TokenKind::Invariant => "invariant",
                TokenKind::Elif => "elif",
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

        // Allow integer literals as path segments (e.g., `compiler.70.backend`)
        if let TokenKind::Integer(n) = &self.current.kind {
            let name = n.to_string();
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
            TokenKind::Gpu => "gpu",
            TokenKind::Me => "me",
            TokenKind::Var => "var",
            TokenKind::Alias => "alias",
            TokenKind::Bitfield => "bitfield",
            TokenKind::Common => "common",
            TokenKind::Export => "export",
            TokenKind::Import => "import",
            TokenKind::Extern => "extern",
            TokenKind::Static => "static",
            TokenKind::Const => "const",
            TokenKind::Impl => "impl",
            TokenKind::Trait => "trait",
            TokenKind::Mixin => "mixin",
            TokenKind::Struct => "struct",
            TokenKind::Class => "class",
            TokenKind::Enum => "enum",
            TokenKind::Spawn => "spawn",
            TokenKind::Async => "async",
            TokenKind::Await => "await",
            TokenKind::Yield => "yield",
            TokenKind::Pub => "pub",
            TokenKind::Priv => "priv",
            TokenKind::New => "new",
            TokenKind::Self_ => "self",
            TokenKind::Super => "super",
            TokenKind::Macro => "macro",
            TokenKind::Context => "context",
            TokenKind::With => "with",
            TokenKind::Result => "result",
            TokenKind::From => "from",
            TokenKind::Fn => "fn",
            TokenKind::Let => "let",
            TokenKind::Mut => "mut",
            TokenKind::Move => "move",
            TokenKind::Actor => "actor",
            TokenKind::Union => "union",
            TokenKind::Old => "old",
            TokenKind::Shared => "shared",
            TokenKind::To => "to",
            TokenKind::NotTo => "not_to",
            TokenKind::Out => "out",
            TokenKind::OutErr => "out_err",
            TokenKind::Pass => "pass",
            TokenKind::PassDoNothing => "pass_do_nothing",
            TokenKind::PassDn => "pass_dn",
            TokenKind::PassTodo => "pass_todo",
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
            TokenKind::Me => "me",
            TokenKind::Alias => "alias",
            TokenKind::Bitfield => "bitfield",
            TokenKind::Pass => "pass",
            TokenKind::PassDoNothing => "pass_do_nothing",
            TokenKind::PassDn => "pass_dn",
            TokenKind::PassTodo => "pass_todo",
            TokenKind::Gpu => "gpu",
            TokenKind::Var => "var",
            TokenKind::Context => "context",
            TokenKind::From => "from",
            TokenKind::Fn => "fn",
            TokenKind::Static => "static",
            TokenKind::Async => "async",
            TokenKind::Await => "await",
            TokenKind::Yield => "yield",
            TokenKind::Spawn => "spawn",
            TokenKind::Move => "move",
            TokenKind::Self_ => "self",
            TokenKind::Let => "let",
            TokenKind::Const => "const",
            TokenKind::Extern => "extern",
            TokenKind::Mut => "mut",
            TokenKind::Shared => "shared",
            TokenKind::With => "with",
            TokenKind::Old => "old",
            TokenKind::Macro => "macro",
            TokenKind::Nil => "nil",
            TokenKind::Mod => "module",
            TokenKind::Import => "import",
            TokenKind::Export => "export",
            TokenKind::Requires => "requires",
            TokenKind::Ensures => "ensures",
            TokenKind::Invariant => "invariant",
            TokenKind::Struct => "struct",
            TokenKind::Class => "class",
            TokenKind::Enum => "enum",
            TokenKind::Trait => "trait",
            TokenKind::Mixin => "mixin",
            TokenKind::Impl => "impl",
            TokenKind::Union => "union",
            TokenKind::Actor => "actor",
            TokenKind::Use => "use",
            TokenKind::Case => "case",
            TokenKind::Auto => "auto",
            TokenKind::Dyn => "dyn",
            TokenKind::Vec => "vec",
            TokenKind::Common => "common",
            TokenKind::Pub => "pub",
            TokenKind::Priv => "priv",
            TokenKind::Def => "def",
            TokenKind::Where => "where",
            TokenKind::Crate => "crate",
            TokenKind::Super => "super",
            // Infix keywords can also be method names
            TokenKind::To => "to",
            TokenKind::NotTo => "not_to",
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

    /// Parse generic type parameters: <T, U, V> or [T, U, V]
    /// Both angle brackets and square brackets are supported for compatibility
    /// Returns empty Vec if no generic parameters are present
    pub(crate) fn parse_generic_params(&mut self) -> Result<Vec<String>, ParseError> {
        // Check for angle brackets <T> or square brackets [T]
        let use_brackets = if self.check(&TokenKind::Lt) {
            self.advance(); // consume '<'
            false
        } else if self.check(&TokenKind::LBracket) {
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

        // Skip whitespace after opening delimiter (for multi-line generic params)
        self.skip_whitespace_tokens();

        while !self.check(&end_token) {
            // Handle const generic: const N: usize
            if self.check(&TokenKind::Const) {
                self.advance(); // consume 'const'
            }
            let name = self.expect_identifier()?;
            // Skip optional type bound: T: Bound or const N: usize
            if self.check(&TokenKind::Colon) {
                self.advance(); // consume ':'
                let _bound = self.parse_type()?; // consume the bound/type
            }
            // Skip optional default value: Rhs = Self, T = DefaultType
            if self.check(&TokenKind::Assign) {
                self.advance(); // consume '='
                let _default = self.parse_type()?; // consume the default type
            }
            params.push(name);

            // Skip whitespace after parameter
            self.skip_whitespace_tokens();

            if !self.check(&end_token) {
                self.expect(&TokenKind::Comma)?;
                // Skip whitespace after comma
                self.skip_whitespace_tokens();
            }
        }

        if use_brackets {
            self.expect(&TokenKind::RBracket)?; // consume ']'
        } else {
            self.expect(&TokenKind::Gt)?; // consume '>'
        }

        Ok(params)
    }
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
