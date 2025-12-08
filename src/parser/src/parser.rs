use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::Lexer;
use crate::token::{Token, TokenKind, Span};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    previous: Token,
    source: &'a str,
    pending_token: Option<Token>,
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
        }
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

    fn parse_item(&mut self) -> Result<Node, ParseError> {
        // Skip leading newlines
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        match &self.current.kind {
            TokenKind::Fn => self.parse_function(),
            TokenKind::Struct => self.parse_struct(),
            TokenKind::Class => self.parse_class(),
            TokenKind::Enum => self.parse_enum(),
            TokenKind::Trait => self.parse_trait(),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Actor => self.parse_actor(),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item()
            }
            TokenKind::Mut => self.parse_mut_let(),
            TokenKind::Let => self.parse_let(),
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => self.parse_static(),
            TokenKind::Type => self.parse_type_alias(),
            TokenKind::Extern => self.parse_extern(),
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match_stmt(),
            TokenKind::For => self.parse_for(),
            TokenKind::While => self.parse_while(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => self.parse_break(),
            TokenKind::Continue => self.parse_continue(),
            TokenKind::Context => self.parse_context(),
            _ => self.parse_expression_or_assignment(),
        }
    }

    fn parse_pub_item(&mut self) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function()?;
                if let Node::Function(ref mut f) = node {
                    f.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct()?;
                if let Node::Struct(ref mut s) = node {
                    s.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class()?;
                if let Node::Class(ref mut c) = node {
                    c.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum()?;
                if let Node::Enum(ref mut e) = node {
                    e.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait()?;
                if let Node::Trait(ref mut t) = node {
                    t.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Actor => {
                let mut node = self.parse_actor()?;
                if let Node::Actor(ref mut a) = node {
                    a.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Const => {
                let mut node = self.parse_const()?;
                if let Node::Const(ref mut c) = node {
                    c.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Static => {
                let mut node = self.parse_static()?;
                if let Node::Static(ref mut s) = node {
                    s.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Type => {
                let mut node = self.parse_type_alias()?;
                if let Node::TypeAlias(ref mut t) = node {
                    t.is_public = true;
                }
                Ok(node)
            }
            TokenKind::Extern => {
                let mut node = self.parse_extern()?;
                if let Node::Extern(ref mut e) = node {
                    e.is_public = true;
                }
                Ok(node)
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, trait, actor, const, static, type, or extern after 'pub'",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Function Parsing ===

    fn parse_function(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Function(FunctionDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            params,
            return_type,
            body,
            is_public: false,
            effect: None,
        }))
    }

    fn parse_parameters(&mut self) -> Result<Vec<Parameter>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();

        while !self.check(&TokenKind::RParen) {
            let param_span = self.current.span;
            let is_mutable = if self.check(&TokenKind::Mut) {
                self.advance();
                true
            } else {
                false
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
                is_mutable,
            });

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;

        // Expect NEWLINE then INDENT
        self.expect(&TokenKind::Newline)?;
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
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            statements,
        })
    }

    // === Type Parsing ===

    fn parse_type(&mut self) -> Result<Type, ParseError> {
        // Parse the first type
        let first = self.parse_single_type()?;

        // Check for union types (A | B | C)
        if self.check(&TokenKind::Pipe) {
            let mut types = vec![first];
            while self.check(&TokenKind::Pipe) {
                self.advance();
                types.push(self.parse_single_type()?);
            }
            return Ok(Type::Union(types));
        }

        Ok(first)
    }

    fn parse_single_type(&mut self) -> Result<Type, ParseError> {
        // Handle pointer types
        match &self.current.kind {
            TokenKind::Ampersand => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer { kind: PointerKind::Unique, inner: Box::new(inner) });
            }
            TokenKind::Star => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer { kind: PointerKind::Shared, inner: Box::new(inner) });
            }
            TokenKind::Minus => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer { kind: PointerKind::Weak, inner: Box::new(inner) });
            }
            TokenKind::Plus => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer { kind: PointerKind::Handle, inner: Box::new(inner) });
            }
            _ => {}
        }

        // Handle tuple type
        if self.check(&TokenKind::LParen) {
            self.advance();
            let mut types = Vec::new();
            while !self.check(&TokenKind::RParen) {
                types.push(self.parse_type()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;

            // Check if it's a function type
            if self.check(&TokenKind::Arrow) {
                self.advance();
                let ret = self.parse_type()?;
                return Ok(Type::Function { params: types, ret: Some(Box::new(ret)) });
            }

            return Ok(Type::Tuple(types));
        }

        // Handle array type
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let element = self.parse_type()?;
            self.expect(&TokenKind::RBracket)?;
            return Ok(Type::Array { element: Box::new(element), size: None });
        }

        // Simple or generic type
        let name = self.expect_identifier()?;

        // Check for generic arguments
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RBracket) {
                args.push(self.parse_type()?);
                if !self.check(&TokenKind::RBracket) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RBracket)?;
            return Ok(Type::Generic { name, args });
        }

        // Check for optional
        if self.check(&TokenKind::Question) {
            self.advance();
            return Ok(Type::Optional(Box::new(Type::Simple(name))));
        }

        Ok(Type::Simple(name))
    }

    // === Statement Parsing ===

    fn parse_mut_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mut)?;
        self.expect(&TokenKind::Let)?;

        let pattern = self.parse_pattern()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Let(LetStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            ty,
            value,
            is_mutable: true,
        }))
    }

    fn parse_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Let)?;

        let is_mutable = if self.check(&TokenKind::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let pattern = self.parse_pattern()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Let(LetStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            ty,
            value,
            is_mutable,
        }))
    }

    fn parse_const(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Const)?;

        let name = self.expect_identifier()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expression()?;

        Ok(Node::Const(ConstStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            ty,
            value,
            is_public: false,
        }))
    }

    fn parse_static(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Static)?;

        let is_mutable = if self.check(&TokenKind::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let name = self.expect_identifier()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expression()?;

        Ok(Node::Static(StaticStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            ty,
            value,
            is_mutable,
            is_public: false,
        }))
    }

    fn parse_type_alias(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        Ok(Node::TypeAlias(TypeAliasDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            ty,
            is_public: false,
        }))
    }

    fn parse_extern(&mut self) -> Result<Node, ParseError> {
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
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            params,
            return_type,
            is_public: false,
        }))
    }

    fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        let condition = self.parse_expression()?;
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
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            condition,
            then_block,
            elif_branches,
            else_block,
        }))
    }

    fn parse_for(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;

        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::For(ForStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            iterable,
            body,
        }))
    }

    fn parse_while(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;

        let condition = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::While(WhileStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            condition,
            body,
        }))
    }

    fn parse_loop(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Loop)?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Loop(LoopStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            body,
        }))
    }

    fn parse_context(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        let context = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Context(ContextStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            context,
            body,
        }))
    }

    fn parse_return(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Return)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Return(ReturnStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            value,
        }))
    }

    fn parse_break(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Break)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Break(BreakStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            value,
        }))
    }

    fn parse_continue(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Continue)?;

        Ok(Node::Continue(ContinueStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
        }))
    }

    fn parse_match_stmt(&mut self) -> Result<Node, ParseError> {
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
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            subject,
            arms,
        }))
    }

    fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;
        let pattern = self.parse_pattern()?;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(&TokenKind::FatArrow)?;

        // Body can be single expression or block
        let body = if self.check(&TokenKind::Newline) {
            self.parse_block()?
        } else {
            let expr = self.parse_expression()?;
            Block {
                span: self.previous.span,
                statements: vec![Node::Expression(expr)],
            }
        };

        Ok(MatchArm {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            guard,
            body,
        })
    }

    // === Type Definition Parsing ===

    fn parse_struct(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            fields.push(self.parse_field()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Struct(StructDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            fields,
            is_public: false,
        }))
    }

    fn parse_class(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Class)?;
        let name = self.expect_identifier()?;

        let parent = if self.check(&TokenKind::LParen) {
            self.advance();
            let p = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(p)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Pub) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                fields.push(self.parse_field()?);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Class(ClassDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            fields,
            methods,
            parent,
            is_public: false,
        }))
    }

    fn parse_enum(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Enum)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut variants = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            variants.push(self.parse_enum_variant()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Enum(EnumDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            variants,
            is_public: false,
        }))
    }

    fn parse_enum_variant(&mut self) -> Result<EnumVariant, ParseError> {
        let start_span = self.current.span;
        let name = self.expect_identifier()?;

        let fields = if self.check(&TokenKind::LParen) {
            self.advance();
            let mut types = Vec::new();
            while !self.check(&TokenKind::RParen) {
                types.push(self.parse_type()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Some(types)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(EnumVariant {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            fields,
        })
    }

    fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            let item = self.parse_function()?;
            if let Node::Function(f) = item {
                methods.push(f);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Trait(TraitDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            methods,
            is_public: false,
        }))
    }

    fn parse_impl(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        let first_name = self.expect_identifier()?;

        let (trait_name, target_type) = if self.check(&TokenKind::For) {
            self.advance();
            let target = self.parse_type()?;
            (Some(first_name), target)
        } else {
            (None, Type::Simple(first_name))
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            let item = self.parse_function()?;
            if let Node::Function(f) = item {
                methods.push(f);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Impl(ImplBlock {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            target_type,
            trait_name,
            methods,
        }))
    }

    fn parse_actor(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Actor)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Pub) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                fields.push(self.parse_field()?);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Actor(ActorDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            fields,
            methods,
            is_public: false,
        }))
    }

    fn parse_field(&mut self) -> Result<Field, ParseError> {
        let start_span = self.current.span;

        let is_public = if self.check(&TokenKind::Pub) {
            self.advance();
            true
        } else {
            false
        };

        let is_mutable = if self.check(&TokenKind::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let default = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(Field {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            ty,
            default,
            is_mutable,
            is_public,
        })
    }

    // === Expression Parsing (Pratt Parser) ===

    fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_or()
    }

    fn parse_expression_or_assignment(&mut self) -> Result<Node, ParseError> {
        let expr = self.parse_expression()?;

        // Check for assignment
        let assign_op = match &self.current.kind {
            TokenKind::Assign => Some(AssignOp::Assign),
            TokenKind::PlusAssign => Some(AssignOp::AddAssign),
            TokenKind::MinusAssign => Some(AssignOp::SubAssign),
            TokenKind::StarAssign => Some(AssignOp::MulAssign),
            TokenKind::SlashAssign => Some(AssignOp::DivAssign),
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
            // Check for no-parentheses call at statement level
            // Only for identifiers or field access followed by argument-starting tokens
            if self.is_callable_expr(&expr) && self.can_start_argument() {
                let args = self.parse_no_paren_arguments()?;
                if !args.is_empty() {
                    let call_expr = match expr {
                        Expr::Identifier(_) => Expr::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        Expr::FieldAccess { receiver, field } => Expr::MethodCall {
                            receiver,
                            method: field,
                            args,
                        },
                        _ => Expr::Call {
                            callee: Box::new(expr),
                            args,
                        },
                    };
                    return Ok(Node::Expression(call_expr));
                }
            }
            Ok(Node::Expression(expr))
        }
    }

    /// Check if an expression can be a callee for no-parens calls
    fn is_callable_expr(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Identifier(_) | Expr::FieldAccess { .. } | Expr::Path(_))
    }

    /// Check if current token can start an argument (for no-parens calls)
    fn can_start_argument(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Integer(_)
                | TokenKind::Float(_)
                | TokenKind::String(_)
                | TokenKind::FString(_)
                | TokenKind::Bool(_)
                | TokenKind::Nil
                | TokenKind::Symbol(_)
                | TokenKind::Identifier(_)
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
                | TokenKind::Backslash
                | TokenKind::Colon  // for named args like name: "value"
        )
    }

    /// Parse arguments without parentheses (comma-separated on same line)
    fn parse_no_paren_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        let mut args = Vec::new();

        // Parse first argument
        if let Ok(arg) = self.parse_single_argument() {
            args.push(arg);
        } else {
            return Ok(args);
        }

        // Parse remaining comma-separated arguments
        while self.check(&TokenKind::Comma) {
            self.advance();
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
                let value = self.parse_expression()?;
                return Ok(Argument {
                    name: Some(name_clone),
                    value,
                });
            }
        }
        // Positional argument
        let value = self.parse_expression()?;
        Ok(Argument { name: None, value })
    }

    /// Peek at the next token kind
    fn peek_is(&self, kind: &TokenKind) -> bool {
        // This is a simple implementation - we'd need to look at the next token
        // For now, we'll handle this differently
        false
    }

    // Binary expression parsing with precedence
    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;

        while self.check(&TokenKind::Or) {
            self.advance();
            let right = self.parse_and()?;
            left = Expr::Binary {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_equality()?;

        while self.check(&TokenKind::And) {
            self.advance();
            let right = self.parse_equality()?;
            left = Expr::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;

        loop {
            let op = match &self.current.kind {
                TokenKind::Eq => BinOp::Eq,
                TokenKind::NotEq => BinOp::NotEq,
                TokenKind::Is => BinOp::Is,
                TokenKind::In => BinOp::In,
                _ => break,
            };
            self.advance();
            let right = self.parse_comparison()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_bitwise_or()?;

        loop {
            let op = match &self.current.kind {
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::LtEq => BinOp::LtEq,
                TokenKind::GtEq => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_bitwise_or()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_bitwise_xor()?;

        while self.check(&TokenKind::Pipe) {
            self.advance();
            let right = self.parse_bitwise_xor()?;
            left = Expr::Binary {
                op: BinOp::BitOr,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_bitwise_and()?;

        while self.check(&TokenKind::Caret) {
            self.advance();
            let right = self.parse_bitwise_and()?;
            left = Expr::Binary {
                op: BinOp::BitXor,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_shift()?;

        while self.check(&TokenKind::Ampersand) {
            self.advance();
            let right = self.parse_shift()?;
            left = Expr::Binary {
                op: BinOp::BitAnd,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_shift(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_term()?;

        loop {
            let op = match &self.current.kind {
                TokenKind::ShiftLeft => BinOp::ShiftLeft,
                TokenKind::ShiftRight => BinOp::ShiftRight,
                _ => break,
            };
            self.advance();
            let right = self.parse_term()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_term(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_factor()?;

        loop {
            let op = match &self.current.kind {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let right = self.parse_factor()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_power()?;

        loop {
            let op = match &self.current.kind {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,
                TokenKind::Percent => BinOp::Mod,
                TokenKind::DoubleSlash => BinOp::FloorDiv,
                _ => break,
            };
            self.advance();
            let right = self.parse_power()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_power(&mut self) -> Result<Expr, ParseError> {
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

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
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
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Ref,
                    operand: Box::new(operand),
                })
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
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            match &self.current.kind {
                TokenKind::LParen => {
                    expr = self.parse_call(expr)?;
                }
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expression()?;
                    self.expect(&TokenKind::RBracket)?;
                    expr = Expr::Index {
                        receiver: Box::new(expr),
                        index: Box::new(index),
                    };
                }
                TokenKind::Dot => {
                    self.advance();
                    let field = self.expect_identifier()?;
                    if self.check(&TokenKind::LParen) {
                        let mut args = self.parse_arguments()?;
                        // Check for trailing block: obj.method(args) \x: body
                        if self.check(&TokenKind::Backslash) {
                            let trailing_lambda = self.parse_trailing_lambda()?;
                            args.push(Argument { name: None, value: trailing_lambda });
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
                            args: vec![Argument { name: None, value: trailing_lambda }],
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
                    let method = self.expect_identifier()?;
                    let args = self.parse_arguments()?;
                    expr = Expr::FunctionalUpdate {
                        target: Box::new(expr),
                        method,
                        args,
                    };
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn parse_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mut args = self.parse_arguments()?;
        // Check for trailing block: func(args) \x: body
        if self.check(&TokenKind::Backslash) {
            let trailing_lambda = self.parse_trailing_lambda()?;
            args.push(Argument { name: None, value: trailing_lambda });
        }
        Ok(Expr::Call {
            callee: Box::new(callee),
            args,
        })
    }

    /// Parse a trailing block lambda: \params: body
    fn parse_trailing_lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::Backslash)?;
        let mut params = Vec::new();

        // Check for no-param lambda: \: expr
        if !self.check(&TokenKind::Colon) {
            // Parse first param name
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });

            // Parse additional params (comma-separated)
            while self.check(&TokenKind::Comma) {
                self.advance();
                let name = self.expect_identifier()?;
                params.push(LambdaParam { name, ty: None });
            }
        }

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_expression()?;
        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
        })
    }

    fn parse_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();

        while !self.check(&TokenKind::RParen) {
            // Check for named argument
            let mut name = None;
            if let TokenKind::Identifier(id) = &self.current.kind {
                let id_clone = id.clone();
                // Peek ahead for '=' without consuming the stream
                let next = self.pending_token.clone().unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Assign {
                    name = Some(id_clone);
                    self.advance(); // consume identifier
                    self.expect(&TokenKind::Assign)?; // consume '='
                } else {
                    // leave current untouched; pending_token already holds the peeked token
                }
            }

            let value = self.parse_expression()?;
            args.push(Argument { name, value });

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Integer(n) => {
                let n = *n;
                self.advance();
                Ok(Expr::Integer(n))
            }
            TokenKind::Float(n) => {
                let n = *n;
                self.advance();
                Ok(Expr::Float(n))
            }
            TokenKind::String(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::String(s))
            }
            TokenKind::FString(parts) => {
                use crate::token::FStringToken;
                use crate::ast::FStringPart;
                let parts = parts.clone();
                self.advance();
                let mut result_parts = Vec::new();
                for part in parts {
                    match part {
                        FStringToken::Literal(s) => {
                            result_parts.push(FStringPart::Literal(s));
                        }
                        FStringToken::Expr(expr_str) => {
                            // Parse the expression string
                            let mut sub_parser = Parser::new(&expr_str);
                            match sub_parser.parse_expression() {
                                Ok(expr) => result_parts.push(FStringPart::Expr(expr)),
                                Err(e) => return Err(e),
                            }
                        }
                    }
                }
                Ok(Expr::FString(result_parts))
            }
            TokenKind::Bool(b) => {
                let b = *b;
                self.advance();
                Ok(Expr::Bool(b))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Expr::Nil)
            }
            TokenKind::Symbol(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::Symbol(s))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();
                // Check for path expression: Name::Variant
                if self.check(&TokenKind::DoubleColon) {
                    let mut segments = vec![name];
                    while self.check(&TokenKind::DoubleColon) {
                        self.advance(); // consume '::'
                        let segment = self.expect_identifier()?;
                        segments.push(segment);
                    }
                    Ok(Expr::Path(segments))
                // Check for struct initialization: Name { field: value, ... }
                // Convention: struct names start with uppercase
                } else if self.check(&TokenKind::LBrace) && name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    self.advance(); // consume '{'
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        self.expect(&TokenKind::Colon)?;
                        let value = self.parse_expression()?;
                        fields.push((field_name, value));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    Ok(Expr::StructInit { name, fields })
                } else {
                    Ok(Expr::Identifier(name))
                }
            }
            TokenKind::Self_ => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
            TokenKind::Backslash => {
                // Lambda: \x: expr or \x, y: expr or \: expr
                self.advance();
                let mut params = Vec::new();

                // Check for no-param lambda: \: expr
                if !self.check(&TokenKind::Colon) {
                    // Parse first param name
                    let name = self.expect_identifier()?;
                    params.push(LambdaParam { name, ty: None });

                    // Parse additional params (comma-separated)
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        let name = self.expect_identifier()?;
                        params.push(LambdaParam { name, ty: None });
                    }
                }

                self.expect(&TokenKind::Colon)?;
                let body = self.parse_expression()?;
                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                })
            }
            TokenKind::LParen => {
                self.advance();
                // Check for lambda: (x, y) => expr
                // Or tuple: (1, 2, 3)
                // Or grouping: (expr)
                if self.check(&TokenKind::RParen) {
                    self.advance();
                    // Empty tuple or lambda with no params
                    if self.check(&TokenKind::FatArrow) {
                        self.advance();
                        let body = self.parse_expression()?;
                        return Ok(Expr::Lambda {
                            params: vec![],
                            body: Box::new(body),
                        });
                    }
                    return Ok(Expr::Tuple(vec![]));
                }

                let first = self.parse_expression()?;

                if self.check(&TokenKind::Comma) {
                    // Tuple
                    let mut elements = vec![first];
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        elements.push(self.parse_expression()?);
                    }
                    self.expect(&TokenKind::RParen)?;
                    Ok(Expr::Tuple(elements))
                } else {
                    // Grouping
                    self.expect(&TokenKind::RParen)?;
                    Ok(first)
                }
            }
            TokenKind::LBracket => {
                self.advance();
                let mut elements = Vec::new();
                while !self.check(&TokenKind::RBracket) {
                    elements.push(self.parse_expression()?);
                    if !self.check(&TokenKind::RBracket) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Expr::Array(elements))
            }
            TokenKind::LBrace => {
                self.advance();
                let mut pairs = Vec::new();
                while !self.check(&TokenKind::RBrace) {
                    let key = self.parse_expression()?;
                    self.expect(&TokenKind::Colon)?;
                    let value = self.parse_expression()?;
                    pairs.push((key, value));
                    if !self.check(&TokenKind::RBrace) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok(Expr::Dict(pairs))
            }
            TokenKind::Spawn => {
                self.advance();
                let expr = self.parse_expression()?;
                Ok(Expr::Spawn(Box::new(expr)))
            }
            TokenKind::New => {
                self.advance();
                // new &Type(...) or new *Type(...)
                let kind = match &self.current.kind {
                    TokenKind::Ampersand => { self.advance(); PointerKind::Unique }
                    TokenKind::Star => { self.advance(); PointerKind::Shared }
                    TokenKind::Minus => { self.advance(); PointerKind::Weak }
                    TokenKind::Plus => { self.advance(); PointerKind::Handle }
                    _ => PointerKind::Shared, // default
                };
                let expr = self.parse_postfix()?;
                Ok(Expr::New {
                    kind,
                    expr: Box::new(expr),
                })
            }
            TokenKind::If => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let then_branch = self.parse_expression()?;
                let else_branch = if self.check(&TokenKind::Else) {
                    self.advance();
                    self.expect(&TokenKind::Colon)?;
                    Some(Box::new(self.parse_expression()?))
                } else {
                    None
                };
                Ok(Expr::If {
                    condition: Box::new(condition),
                    then_branch: Box::new(then_branch),
                    else_branch,
                })
            }
            _ => Err(ParseError::unexpected_token(
                "expression",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Pattern Parsing ===

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            TokenKind::Mut => {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(Pattern::MutIdentifier(name))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();

                // Check for struct pattern: Name { ... }
                if self.check(&TokenKind::LBrace) {
                    self.advance();
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        let pattern = if self.check(&TokenKind::Colon) {
                            self.advance();
                            self.parse_pattern()?
                        } else {
                            Pattern::Identifier(field_name.clone())
                        };
                        fields.push((field_name, pattern));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Pattern::Struct { name, fields });
                }

                // Check for enum variant: Name::Variant or Name::Variant(...)
                if self.check(&TokenKind::DoubleColon) {
                    self.advance();
                    let variant = self.expect_identifier()?;
                    let payload = if self.check(&TokenKind::LParen) {
                        self.advance();
                        let mut patterns = Vec::new();
                        while !self.check(&TokenKind::RParen) {
                            patterns.push(self.parse_pattern()?);
                            if !self.check(&TokenKind::RParen) {
                                self.expect(&TokenKind::Comma)?;
                            }
                        }
                        self.expect(&TokenKind::RParen)?;
                        Some(patterns)
                    } else {
                        None
                    };
                    return Ok(Pattern::Enum { name, variant, payload });
                }

                Ok(Pattern::Identifier(name))
            }
            TokenKind::Integer(_) | TokenKind::Float(_) | TokenKind::String(_)
            | TokenKind::Bool(_) | TokenKind::Nil => {
                let expr = self.parse_primary()?;
                Ok(Pattern::Literal(Box::new(expr)))
            }
            TokenKind::LParen => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RParen) {
                    patterns.push(self.parse_pattern()?);
                    if !self.check(&TokenKind::RParen) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Pattern::Tuple(patterns))
            }
            TokenKind::LBracket => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RBracket) {
                    if self.check(&TokenKind::Ellipsis) {
                        self.advance();
                        patterns.push(Pattern::Rest);
                    } else {
                        patterns.push(self.parse_pattern()?);
                    }
                    if !self.check(&TokenKind::RBracket) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Pattern::Array(patterns))
            }
            _ => Err(ParseError::unexpected_token(
                "pattern",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Helper Methods ===

    fn advance(&mut self) {
        self.previous = std::mem::replace(
            &mut self.current,
            self.pending_token.take().unwrap_or_else(|| self.lexer.next_token())
        );
    }

    fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current.kind) == std::mem::discriminant(kind)
    }

    fn is_at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    fn expect(&mut self, kind: &TokenKind) -> Result<(), ParseError> {
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

    fn expect_identifier(&mut self) -> Result<String, ParseError> {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    fn parse(source: &str) -> Result<Module, ParseError> {
        let mut parser = Parser::new(source);
        parser.parse()
    }

    // === Expression Tests ===

    #[test]
    fn test_integer_literal() {
        let module = parse("42").unwrap();
        assert_eq!(module.items.len(), 1);
        if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
            assert_eq!(*n, 42);
        } else {
            panic!("Expected integer expression");
        }
    }

    #[test]
    fn test_binary_expression() {
        let module = parse("1 + 2").unwrap();
        assert_eq!(module.items.len(), 1);
        if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
            assert_eq!(*op, BinOp::Add);
            assert_eq!(**left, Expr::Integer(1));
            assert_eq!(**right, Expr::Integer(2));
        } else {
            panic!("Expected binary expression");
        }
    }

    #[test]
    fn test_operator_precedence() {
        let module = parse("1 + 2 * 3").unwrap();
        // Should parse as 1 + (2 * 3)
        if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
            assert_eq!(*op, BinOp::Add);
            assert_eq!(**left, Expr::Integer(1));
            if let Expr::Binary { op: inner_op, .. } = &**right {
                assert_eq!(*inner_op, BinOp::Mul);
            } else {
                panic!("Expected nested binary");
            }
        } else {
            panic!("Expected binary expression");
        }
    }

    #[test]
    fn test_function_call() {
        let module = parse("foo(1, 2)").unwrap();
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            assert_eq!(**callee, Expr::Identifier("foo".to_string()));
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected call expression");
        }
    }

    #[test]
    fn test_method_call() {
        let module = parse("obj.method(x)").unwrap();
        if let Node::Expression(Expr::MethodCall { receiver, method, args }) = &module.items[0] {
            assert_eq!(**receiver, Expr::Identifier("obj".to_string()));
            assert_eq!(method, "method");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected method call");
        }
    }

    #[test]
    fn test_array_literal() {
        let module = parse("[1, 2, 3]").unwrap();
        if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
            assert_eq!(elements.len(), 3);
        } else {
            panic!("Expected array literal");
        }
    }

    // === Statement Tests ===

    #[test]
    fn test_let_statement() {
        let module = parse("let x = 42").unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            assert!(!stmt.is_mutable);
            if let Pattern::Identifier(name) = &stmt.pattern {
                assert_eq!(name, "x");
            }
        } else {
            panic!("Expected let statement");
        }
    }

    #[test]
    fn test_let_mut_statement() {
        let module = parse("let mut x = 42").unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            assert!(stmt.is_mutable);
        } else {
            panic!("Expected let statement");
        }
    }

    // === Function Tests ===

    #[test]
    fn test_function_definition() {
        let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
        let module = parse(source).unwrap();
        if let Node::Function(func) = &module.items[0] {
            assert_eq!(func.name, "add");
            assert_eq!(func.params.len(), 2);
            assert!(func.return_type.is_some());
        } else {
            panic!("Expected function definition");
        }
    }

    #[test]
    fn test_simple_function() {
        let source = "fn greet():\n    print(\"hello\")";
        let module = parse(source).unwrap();
        if let Node::Function(func) = &module.items[0] {
            assert_eq!(func.name, "greet");
            assert_eq!(func.params.len(), 0);
        } else {
            panic!("Expected function definition");
        }
    }

    // === Struct Tests ===

    #[test]
    fn test_struct_definition() {
        let source = "struct Point:\n    x: f64\n    y: f64";
        let module = parse(source).unwrap();
        if let Node::Struct(s) = &module.items[0] {
            assert_eq!(s.name, "Point");
            assert_eq!(s.fields.len(), 2);
        } else {
            panic!("Expected struct definition");
        }
    }

    // === Enum Tests ===

    #[test]
    fn test_enum_definition() {
        let source = "enum Option:\n    Some(i64)\n    None";
        let module = parse(source).unwrap();
        if let Node::Enum(e) = &module.items[0] {
            assert_eq!(e.name, "Option");
            assert_eq!(e.variants.len(), 2);
        } else {
            panic!("Expected enum definition");
        }
    }

    // === Control Flow Tests ===

    #[test]
    fn test_if_statement() {
        let source = "if x > 0:\n    print(x)";
        let module = parse(source).unwrap();
        if let Node::If(stmt) = &module.items[0] {
            assert!(stmt.else_block.is_none());
            assert!(stmt.elif_branches.is_empty());
        } else {
            panic!("Expected if statement");
        }
    }

    #[test]
    fn test_for_loop() {
        let source = "for i in range(10):\n    print(i)";
        let module = parse(source).unwrap();
        if let Node::For(stmt) = &module.items[0] {
            if let Pattern::Identifier(name) = &stmt.pattern {
                assert_eq!(name, "i");
            }
        } else {
            panic!("Expected for statement");
        }
    }

    #[test]
    fn test_while_loop() {
        let source = "while x > 0:\n    x = x - 1";
        let module = parse(source).unwrap();
        assert!(matches!(&module.items[0], Node::While(_)));
    }

    // === Pattern Tests ===

    #[test]
    fn test_tuple_pattern() {
        let source = "let (x, y) = point";
        let module = parse(source).unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            if let Pattern::Tuple(patterns) = &stmt.pattern {
                assert_eq!(patterns.len(), 2);
            } else {
                panic!("Expected tuple pattern");
            }
        }
    }
}
