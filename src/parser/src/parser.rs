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
            // Skip newlines at top level
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }

            items.push(self.parse_item()?);
        }

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
            TokenKind::Struct => self.parse_struct_with_doc(doc_comment),
            TokenKind::Class => self.parse_class_with_doc(doc_comment),
            TokenKind::Enum => self.parse_enum_with_doc(doc_comment),
            TokenKind::Union => self.parse_union_with_doc(doc_comment),
            TokenKind::Trait => self.parse_trait_with_doc(doc_comment),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Actor => self.parse_actor(),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_doc(doc_comment)
            }
            TokenKind::Mut => self.parse_mut_let(),
            TokenKind::Let => self.parse_let(),
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => self.parse_static(),
            TokenKind::Shared => self.parse_shared_let(),
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
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match_stmt(),
            TokenKind::For => self.parse_for(),
            TokenKind::While => self.parse_while(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => self.parse_break(),
            TokenKind::Continue => self.parse_continue(),
            TokenKind::Context => self.parse_context(),
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
            f.effects.push(Effect::Async);
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

        // Allow keywords like 'new', 'type', etc. as function names
        let name = self.expect_method_name()?;
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Parse optional where clause: where T: Clone + Default
        let where_clause = self.parse_where_clause()?;

        // Skip newlines before the function body colon
        self.skip_newlines();

        self.expect(&TokenKind::Colon)?;

        // After the colon, expect NEWLINE + INDENT to start the function body
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse optional contract block at the start of the function body
        // (new: in/out/out_err/invariant, legacy: requires/ensures)
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

        // Parse the rest of the function body statements
        let body = self.parse_block_body()?;

        // Check for trailing bounds: block (only valid for @simd decorated functions)
        let has_simd = decorators.iter().any(|d| {
            matches!(&d.name, Expr::Identifier(name) if name == "simd")
        });

        let bounds_block = if has_simd {
            // Skip newlines after body to check for bounds:
            self.skip_newlines();
            self.parse_bounds_block()?
        } else {
            None
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
            effects: vec![],
            decorators,
            attributes,
            doc_comment: None,
            contract,
            is_abstract: false,
            bounds_block,
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

            self.expect(&TokenKind::Colon)?;

            // Parse trait bounds: Trait1 + Trait2 + ...
            let mut trait_bounds = Vec::new();
            loop {
                let bound_name = self.expect_identifier()?;
                trait_bounds.push(bound_name);

                // Check for + to continue parsing bounds
                if self.check(&TokenKind::Plus) {
                    self.advance();
                } else {
                    break;
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
                // Attributes followed by decorators - extract effect decorators
                let mut decorators = Vec::new();
                let mut effects = Vec::new();
                while self.check(&TokenKind::At) {
                    let decorator = self.parse_decorator()?;

                    // Check if this is an effect decorator
                    if let Expr::Identifier(name) = &decorator.name {
                        if let Some(effect) = Effect::from_decorator_name(name) {
                            effects.push(effect);
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            continue;
                        }
                    }

                    decorators.push(decorator);
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                let mut node = self.parse_function_with_attrs(decorators, attributes)?;
                if let Node::Function(ref mut f) = node {
                    f.effects = effects;
                }
                Ok(node)
            }
            TokenKind::Fn => self.parse_function_with_attrs(vec![], attributes),
            TokenKind::Async => {
                self.advance();
                let mut func = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = func {
                    f.effects.push(Effect::Async);
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
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, union, mod, or pub after attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse optional parenthesized argument list: `(arg1, arg2, ...)`
    fn parse_optional_paren_args(&mut self) -> Result<Option<Vec<Expr>>, ParseError> {
        if self.check(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) {
                args.push(self.parse_expression()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
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
    /// Effect decorators (@pure, @io, @net, @fs, @unsafe, @async) are extracted
    /// into the function's effects field; other decorators remain in decorators field.
    fn parse_decorated_function(&mut self) -> Result<Node, ParseError> {
        let mut decorators = Vec::new();
        let mut effects = Vec::new();

        // Parse all decorators (can be multiple: @pure @io fn foo)
        while self.check(&TokenKind::At) {
            let decorator = self.parse_decorator()?;

            // Check if this is an effect decorator
            if let Expr::Identifier(name) = &decorator.name {
                if let Some(effect) = Effect::from_decorator_name(name) {
                    effects.push(effect);
                    // Skip newlines after effect decorator
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    continue;
                }
            }

            // Not an effect decorator - keep as regular decorator
            decorators.push(decorator);

            // Skip newlines between decorators
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the function with the collected decorators and effects
        let mut node = self.parse_function_with_decorators(decorators)?;

        // Set the effects on the function
        if let Node::Function(ref mut f) = node {
            f.effects = effects;
        }

        Ok(node)
    }

    /// Parse a single decorator: @name or @name(args)
    /// Also handles @async which uses a keyword instead of identifier.
    /// Supports named arguments: @bounds(default="return", strict=true)
    fn parse_decorator(&mut self) -> Result<Decorator, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Handle keywords specially since they can be decorator names
        let name = if self.check(&TokenKind::Async) {
            self.advance();
            Expr::Identifier("async".to_string())
        } else if self.check(&TokenKind::Bounds) {
            self.advance();
            Expr::Identifier("bounds".to_string())
        } else {
            // Parse the decorator name (can be dotted: @module.decorator)
            self.parse_primary()?
        };

        // Check for arguments: @decorator(arg1, arg2) or @decorator(name=value)
        let args = if self.check(&TokenKind::LParen) {
            Some(self.parse_arguments()?)
        } else {
            None
        };

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

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
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
        let start_span = self.current.span;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
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
        } else {
            Err(ParseError::unexpected_token(
                "identifier",
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
            // Infix keywords can also be method names
            TokenKind::To => "to",
            TokenKind::NotTo => "not_to",
            // Allow 'with' as method name for SIMD v.with(idx, val)
            TokenKind::With => "with",
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

        while !self.check(&end_token) {
            let name = self.expect_identifier()?;
            params.push(name);

            if !self.check(&end_token) {
                self.expect(&TokenKind::Comma)?;
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
