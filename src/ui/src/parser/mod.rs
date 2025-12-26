//! SUI Template Parser
//!
//! Parses `.sui` template files into an AST.

pub mod ast;
mod parser_expr;

pub use ast::*;

use crate::lexer::{SuiLexer, SuiToken, SuiTokenKind, Span};
use thiserror::Error;

/// Parse error type
#[derive(Debug, Clone, Error)]
pub enum ParseError {
    #[error("Unexpected token: expected {expected}, found {found} at line {line}, column {column}")]
    UnexpectedToken {
        expected: String,
        found: String,
        line: usize,
        column: usize,
    },
    #[error("Unexpected end of file")]
    UnexpectedEof,
    #[error("Invalid template: {message} at line {line}, column {column}")]
    InvalidTemplate {
        message: String,
        line: usize,
        column: usize,
    },
    #[error("Unclosed block: {block_type} at line {line}, column {column}")]
    UnclosedBlock {
        block_type: String,
        line: usize,
        column: usize,
    },
}

/// SUI template parser
pub struct SuiParser<'a> {
    tokens: Vec<SuiToken>,
    current: usize,
    source: &'a str,
}

impl<'a> SuiParser<'a> {
    /// Create a new parser for the given source
    pub fn new(source: &'a str) -> Self {
        let mut lexer = SuiLexer::new(source);
        let tokens = lexer.tokenize();
        Self {
            tokens,
            current: 0,
            source,
        }
    }

    /// Parse the template
    pub fn parse(&mut self) -> Result<SuiTemplate, ParseError> {
        // Look for directive to determine template kind
        let (kind, name, layout, layout_props) = self.parse_template_directive()?;

        let mut template = SuiTemplate::new(kind, name);
        template.layout = layout;
        template.layout_props = layout_props;

        // Parse declarations, server/client blocks, and content
        while !self.is_at_end() {
            match self.peek_kind() {
                SuiTokenKind::DeclOpen => {
                    let decl = self.parse_declaration()?;
                    template.declarations.push(decl);
                }
                SuiTokenKind::ServerOpen => {
                    let block = self.parse_server_block()?;
                    template.server_block = Some(block);
                }
                SuiTokenKind::ClientOpen => {
                    let block = self.parse_client_block()?;
                    template.client_block = Some(block);
                }
                _ => {
                    let node = self.parse_template_node()?;
                    if let Some(node) = node {
                        template.content.push(node);
                    }
                }
            }
        }

        Ok(template)
    }

    /// Parse the template directive `{@ page/component/layout Name @}`
    fn parse_template_directive(&mut self) -> Result<(TemplateKind, String, Option<String>, Vec<(String, Expr)>), ParseError> {
        // Skip any leading content until we find a directive
        while !self.is_at_end() && self.peek_kind() != SuiTokenKind::DirectiveOpen {
            self.advance();
        }

        if self.is_at_end() {
            return Ok((TemplateKind::Component, "Anonymous".to_string(), None, Vec::new()));
        }

        self.expect(SuiTokenKind::DirectiveOpen)?;

        let kind = match self.peek_kind() {
            SuiTokenKind::Page => {
                self.advance();
                TemplateKind::Page
            }
            SuiTokenKind::Component => {
                self.advance();
                TemplateKind::Component
            }
            SuiTokenKind::Layout => {
                self.advance();
                TemplateKind::Layout
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "page, component, or layout".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        let name = self.expect_identifier()?;

        // Parse optional layout and props
        let mut layout = None;
        let mut layout_props = Vec::new();

        while self.peek_kind() != SuiTokenKind::DirectiveClose {
            if let SuiTokenKind::Identifier(key) = self.peek_kind() {
                self.advance();
                if key == "layout" {
                    self.expect(SuiTokenKind::Assign)?;
                    layout = Some(self.expect_identifier()?);
                } else {
                    // It's a prop
                    self.expect(SuiTokenKind::Assign)?;
                    let value = self.parse_expression()?;
                    layout_props.push((key, value));
                }
            } else {
                break;
            }
        }

        self.expect(SuiTokenKind::DirectiveClose)?;

        Ok((kind, name, layout, layout_props))
    }

    /// Parse a state declaration `{$ let name: Type $}`
    fn parse_declaration(&mut self) -> Result<StateDecl, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::DeclOpen)?;
        self.expect(SuiTokenKind::Let)?;

        let name = self.expect_identifier()?;

        let ty = if self.peek_kind() == SuiTokenKind::Colon {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let default = if self.peek_kind() == SuiTokenKind::Assign {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(SuiTokenKind::DeclClose)?;

        Ok(StateDecl {
            span: start.merge(&self.previous().span),
            name,
            ty,
            default,
        })
    }

    /// Parse server block `{- ... -}`
    fn parse_server_block(&mut self) -> Result<ServerBlock, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ServerOpen)?;

        let mut statements = Vec::new();
        while self.peek_kind() != SuiTokenKind::ServerClose && !self.is_at_end() {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        self.expect(SuiTokenKind::ServerClose)?;

        Ok(ServerBlock {
            span: start.merge(&self.previous().span),
            statements,
        })
    }

    /// Parse client block `{+ ... +}`
    fn parse_client_block(&mut self) -> Result<ClientBlock, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ClientOpen)?;

        let mut statements = Vec::new();
        while self.peek_kind() != SuiTokenKind::ClientClose && !self.is_at_end() {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        self.expect(SuiTokenKind::ClientClose)?;

        Ok(ClientBlock {
            span: start.merge(&self.previous().span),
            statements,
        })
    }

    /// Parse a template node (element, text, output, control, etc.)
    fn parse_template_node(&mut self) -> Result<Option<TemplateNode>, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::TagOpen => Ok(Some(self.parse_element()?)),
            SuiTokenKind::TagEndOpen => {
                // Closing tag - return None to let parent handle it
                Ok(None)
            }
            SuiTokenKind::Text(text) => {
                let span = self.peek().span;
                self.advance();
                Ok(Some(TemplateNode::Text(TextNode {
                    span,
                    content: text,
                })))
            }
            SuiTokenKind::OutputOpen => Ok(Some(self.parse_output(false)?)),
            SuiTokenKind::RawOutputOpen => Ok(Some(self.parse_output(true)?)),
            SuiTokenKind::ControlOpen => Ok(Some(self.parse_control()?)),
            SuiTokenKind::DirectiveOpen => Ok(Some(self.parse_template_directive_node()?)),
            SuiTokenKind::CommentOpen => {
                self.advance();
                if let SuiTokenKind::Comment(content) = self.peek_kind() {
                    self.advance();
                    Ok(Some(TemplateNode::Comment(content)))
                } else {
                    Ok(Some(TemplateNode::Comment(String::new())))
                }
            }
            SuiTokenKind::Eof => Ok(None),
            SuiTokenKind::Newline | SuiTokenKind::Whitespace => {
                self.advance();
                Ok(None)
            }
            _ => {
                // Skip unexpected tokens
                self.advance();
                Ok(None)
            }
        }
    }

    /// Parse an HTML element
    fn parse_element(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::TagOpen)?;

        let tag = self.expect_identifier()?;
        let mut element = Element::new(tag.clone());
        element.span = start;

        // Parse attributes
        while !matches!(self.peek_kind(), SuiTokenKind::TagClose | SuiTokenKind::TagSelfClose) {
            if self.is_at_end() {
                return Err(ParseError::UnclosedBlock {
                    block_type: format!("<{}>", tag),
                    line: start.line,
                    column: start.column,
                });
            }
            let attr = self.parse_attribute()?;
            element.attrs.push(attr);
        }

        // Check for self-closing tag
        if self.peek_kind() == SuiTokenKind::TagSelfClose {
            self.advance();
            element.self_closing = true;
            return Ok(TemplateNode::Element(element));
        }

        self.expect(SuiTokenKind::TagClose)?;

        // Parse children until closing tag
        loop {
            if self.is_at_end() {
                return Err(ParseError::UnclosedBlock {
                    block_type: format!("<{}>", tag),
                    line: start.line,
                    column: start.column,
                });
            }

            // Check for closing tag
            if self.peek_kind() == SuiTokenKind::TagEndOpen {
                self.advance();
                let closing_tag = self.expect_identifier()?;
                if closing_tag != tag {
                    return Err(ParseError::InvalidTemplate {
                        message: format!("Mismatched closing tag: expected </{}>, found </{}>", tag, closing_tag),
                        line: self.previous().span.line,
                        column: self.previous().span.column,
                    });
                }
                self.expect(SuiTokenKind::TagClose)?;
                break;
            }

            if let Some(child) = self.parse_template_node()? {
                element.children.push(child);
            }
        }

        element.span = start.merge(&self.previous().span);
        Ok(TemplateNode::Element(element))
    }

    /// Parse an HTML attribute
    fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start = self.peek().span;
        let name = self.expect_identifier()?;

        // Check for special attribute prefixes
        if name.starts_with("on:") {
            // Event handler
            let event = name[3..].to_string();
            self.expect(SuiTokenKind::Assign)?;
            let handler = self.parse_attribute_value_expr()?;
            return Ok(Attribute {
                span: start.merge(&self.previous().span),
                name,
                value: AttributeValue::Event { event, handler },
            });
        }

        if name.starts_with("class:") {
            // Conditional class
            let class = name[6..].to_string();
            self.expect(SuiTokenKind::Assign)?;
            let condition = self.parse_attribute_value_expr()?;
            return Ok(Attribute {
                span: start.merge(&self.previous().span),
                name,
                value: AttributeValue::ConditionalClass { class, condition },
            });
        }

        // Check if there's a value
        if self.peek_kind() != SuiTokenKind::Assign {
            // Boolean attribute
            return Ok(Attribute {
                span: start,
                name,
                value: AttributeValue::Boolean,
            });
        }

        self.expect(SuiTokenKind::Assign)?;

        // Parse value
        let value = match self.peek_kind() {
            SuiTokenKind::String(s) => {
                self.advance();
                AttributeValue::Static(s)
            }
            SuiTokenKind::OutputOpen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(SuiTokenKind::OutputClose)?;
                AttributeValue::Dynamic(expr)
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "string or {{ expression }}".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        Ok(Attribute {
            span: start.merge(&self.previous().span),
            name,
            value,
        })
    }

    /// Parse an attribute value expression (handles both quoted and {{ }})
    fn parse_attribute_value_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::String(s) => {
                self.advance();
                Ok(Expr::String(s))
            }
            SuiTokenKind::OutputOpen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(SuiTokenKind::OutputClose)?;
                Ok(expr)
            }
            _ => self.parse_expression(),
        }
    }

    /// Parse output expression `{{ expr }}` or `{! expr !}`
    fn parse_output(&mut self, raw: bool) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;

        if raw {
            self.expect(SuiTokenKind::RawOutputOpen)?;
        } else {
            self.expect(SuiTokenKind::OutputOpen)?;
        }

        let expr = self.parse_expression()?;

        if raw {
            self.expect(SuiTokenKind::RawOutputClose)?;
        } else {
            self.expect(SuiTokenKind::OutputClose)?;
        }

        let node = OutputNode {
            span: start.merge(&self.previous().span),
            expr,
        };

        if raw {
            Ok(TemplateNode::RawOutput(node))
        } else {
            Ok(TemplateNode::Output(node))
        }
    }

    /// Parse control flow `{% if/for/let %}`
    fn parse_control(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ControlOpen)?;

        let control = match self.peek_kind() {
            SuiTokenKind::If => self.parse_if_control(start)?,
            SuiTokenKind::For => self.parse_for_control(start)?,
            SuiTokenKind::Let => self.parse_let_control(start)?,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "if, for, or let".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        Ok(TemplateNode::Control(control))
    }

    /// Parse if control `{% if condition: %}...{% elif: %}...{% else: %}...{% end %}`
    fn parse_if_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::If)?;
        let condition = self.parse_expression()?;
        self.expect(SuiTokenKind::Colon)?;
        self.expect(SuiTokenKind::ControlClose)?;

        let then_branch = self.parse_control_body()?;

        let mut elif_branches = Vec::new();
        let mut else_branch = None;

        // Parse elif/else branches
        loop {
            if self.peek_kind() != SuiTokenKind::ControlOpen {
                break;
            }

            // Peek ahead to see what kind of control it is
            let saved = self.current;
            self.advance(); // consume {%

            match self.peek_kind() {
                SuiTokenKind::Elif => {
                    self.advance();
                    let elif_condition = self.parse_expression()?;
                    self.expect(SuiTokenKind::Colon)?;
                    self.expect(SuiTokenKind::ControlClose)?;
                    let elif_body = self.parse_control_body()?;
                    elif_branches.push((elif_condition, elif_body));
                }
                SuiTokenKind::Else => {
                    self.advance();
                    self.expect(SuiTokenKind::Colon)?;
                    self.expect(SuiTokenKind::ControlClose)?;
                    else_branch = Some(self.parse_control_body()?);
                    break;
                }
                SuiTokenKind::End => {
                    self.current = saved; // restore position
                    break;
                }
                _ => {
                    self.current = saved;
                    break;
                }
            }
        }

        // Expect end
        self.expect(SuiTokenKind::ControlOpen)?;
        self.expect(SuiTokenKind::End)?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::If(IfNode {
            span: start.merge(&self.previous().span),
            condition,
            then_branch,
            elif_branches,
            else_branch,
        }))
    }

    /// Parse for control `{% for item in collection: %}...{% end %}`
    fn parse_for_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::For)?;
        let binding = self.expect_identifier()?;

        // Optional index binding
        let index_binding = if self.peek_kind() == SuiTokenKind::Comma {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
        };

        self.expect(SuiTokenKind::In)?;
        let iterable = self.parse_expression()?;

        // Optional key expression
        let key = if let SuiTokenKind::Identifier(k) = self.peek_kind() {
            if k == "key" {
                self.advance();
                self.expect(SuiTokenKind::Assign)?;
                Some(self.parse_expression()?)
            } else {
                None
            }
        } else {
            None
        };

        self.expect(SuiTokenKind::Colon)?;
        self.expect(SuiTokenKind::ControlClose)?;

        let body = self.parse_control_body()?;

        self.expect(SuiTokenKind::ControlOpen)?;
        self.expect(SuiTokenKind::End)?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::For(ForNode {
            span: start.merge(&self.previous().span),
            binding,
            index_binding,
            iterable,
            key,
            body,
        }))
    }

    /// Parse let control `{% let name = expr %}`
    fn parse_let_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::Let)?;
        let name = self.expect_identifier()?;
        self.expect(SuiTokenKind::Assign)?;
        let value = self.parse_expression()?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::Let(LetNode {
            span: start.merge(&self.previous().span),
            name,
            value,
        }))
    }

    /// Parse control body (content until {% end/elif/else %})
    fn parse_control_body(&mut self) -> Result<Vec<TemplateNode>, ParseError> {
        let mut nodes = Vec::new();

        loop {
            if self.is_at_end() {
                break;
            }

            // Check for control block
            if self.peek_kind() == SuiTokenKind::ControlOpen {
                // Peek to see if it's end/elif/else
                let saved = self.current;
                self.advance();
                match self.peek_kind() {
                    SuiTokenKind::End | SuiTokenKind::Elif | SuiTokenKind::Else => {
                        self.current = saved;
                        break;
                    }
                    _ => {
                        self.current = saved;
                    }
                }
            }

            if let Some(node) = self.parse_template_node()? {
                nodes.push(node);
            }
        }

        Ok(nodes)
    }

    /// Parse directive node (embed, slot, fill)
    fn parse_template_directive_node(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::DirectiveOpen)?;

        match self.peek_kind() {
            SuiTokenKind::Embed => {
                self.advance();
                let component = self.expect_identifier()?;
                let mut props = Vec::new();
                let mut hydrate = HydrateStrategy::default();

                while self.peek_kind() != SuiTokenKind::DirectiveClose {
                    // Handle both identifiers and the 'hydrate' keyword
                    let key = match self.peek_kind() {
                        SuiTokenKind::Identifier(k) => {
                            self.advance();
                            k
                        }
                        SuiTokenKind::Hydrate => {
                            self.advance();
                            "hydrate".to_string()
                        }
                        _ => break,
                    };

                    self.expect(SuiTokenKind::Assign)?;

                    if key == "hydrate" {
                        if let SuiTokenKind::String(s) = self.peek_kind() {
                            self.advance();
                            hydrate = HydrateStrategy::from_str(&s).unwrap_or_default();
                        }
                    } else {
                        let value = self.parse_expression()?;
                        props.push((key, value));
                    }
                }

                self.expect(SuiTokenKind::DirectiveClose)?;

                Ok(TemplateNode::Embed(EmbedNode {
                    span: start.merge(&self.previous().span),
                    component,
                    props,
                    hydrate,
                }))
            }
            SuiTokenKind::Slot => {
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(SuiTokenKind::DirectiveClose)?;

                Ok(TemplateNode::Slot(SlotNode {
                    span: start.merge(&self.previous().span),
                    name,
                    default: None,
                }))
            }
            SuiTokenKind::Fill => {
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(SuiTokenKind::DirectiveClose)?;

                // Parse content until {@ end @}
                let mut content = Vec::new();
                loop {
                    if self.is_at_end() {
                        break;
                    }
                    if self.peek_kind() == SuiTokenKind::DirectiveOpen {
                        let saved = self.current;
                        self.advance();
                        if self.peek_kind() == SuiTokenKind::End {
                            self.advance();
                            self.expect(SuiTokenKind::DirectiveClose)?;
                            break;
                        }
                        self.current = saved;
                    }
                    if let Some(node) = self.parse_template_node()? {
                        content.push(node);
                    }
                }

                Ok(TemplateNode::Fill(FillNode {
                    span: start.merge(&self.previous().span),
                    name,
                    content,
                }))
            }
            _ => {
                // Skip unknown directives
                while self.peek_kind() != SuiTokenKind::DirectiveClose && !self.is_at_end() {
                    self.advance();
                }
                self.expect(SuiTokenKind::DirectiveClose)?;
                Ok(TemplateNode::Comment("Unknown directive".to_string()))
            }
        }
    }

    // Expression parsing methods are in parser_expr module

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        // Skip newlines
        while self.peek_kind() == SuiTokenKind::Newline {
            self.advance();
        }

        match self.peek_kind() {
            SuiTokenKind::Let => {
                self.advance();
                let name = self.expect_identifier()?;
                let ty = if self.peek_kind() == SuiTokenKind::Colon {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(SuiTokenKind::Assign)?;
                let value = self.parse_expression()?;
                Ok(Statement::Let { name, ty, value })
            }
            SuiTokenKind::If => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let then_block = self.parse_statement_block()?;
                let else_block = if self.peek_kind() == SuiTokenKind::Else {
                    self.advance();
                    self.expect(SuiTokenKind::Colon)?;
                    Some(self.parse_statement_block()?)
                } else {
                    None
                };
                Ok(Statement::If { condition, then_block, else_block })
            }
            SuiTokenKind::For => {
                self.advance();
                let binding = self.expect_identifier()?;
                self.expect(SuiTokenKind::In)?;
                let iterable = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let body = self.parse_statement_block()?;
                Ok(Statement::For { binding, iterable, body })
            }
            SuiTokenKind::While => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let body = self.parse_statement_block()?;
                Ok(Statement::While { condition, body })
            }
            SuiTokenKind::Break => {
                self.advance();
                Ok(Statement::Break)
            }
            SuiTokenKind::Continue => {
                self.advance();
                Ok(Statement::Continue)
            }
            SuiTokenKind::Identifier(name) => {
                self.advance();
                if self.peek_kind() == SuiTokenKind::Assign {
                    self.advance();
                    let value = self.parse_expression()?;
                    Ok(Statement::Assignment { target: name, value })
                } else {
                    // It's an expression starting with identifier
                    // Put it back and parse as expression
                    self.current -= 1;
                    let expr = self.parse_expression()?;
                    Ok(Statement::Expr(expr))
                }
            }
            _ => {
                let expr = self.parse_expression()?;
                Ok(Statement::Expr(expr))
            }
        }
    }

    fn parse_statement_block(&mut self) -> Result<Vec<Statement>, ParseError> {
        // For now, parse single statement (multi-line blocks need indentation handling)
        let stmt = self.parse_statement()?;
        Ok(vec![stmt])
    }

    // ========================================================================
    // Type parsing
    // ========================================================================

    fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.expect_identifier()?;

        // Check for generic args
        if self.peek_kind() == SuiTokenKind::LBracket {
            self.advance();
            let mut args = vec![self.parse_type()?];
            while self.peek_kind() == SuiTokenKind::Comma {
                self.advance();
                args.push(self.parse_type()?);
            }
            self.expect(SuiTokenKind::RBracket)?;
            return Ok(TypeExpr::Generic { name, args });
        }

        Ok(TypeExpr::Named(name))
    }

    // ========================================================================
    // Helper methods
    // ========================================================================

    fn peek(&self) -> &SuiToken {
        &self.tokens[self.current.min(self.tokens.len() - 1)]
    }

    fn peek_kind(&self) -> SuiTokenKind {
        self.peek().kind.clone()
    }

    fn previous(&self) -> &SuiToken {
        &self.tokens[(self.current - 1).max(0)]
    }

    fn advance(&mut self) -> &SuiToken {
        if !self.is_at_end() {
            self.current += 1;
        }
        self.previous()
    }

    fn is_at_end(&self) -> bool {
        self.peek_kind() == SuiTokenKind::Eof
    }

    fn expect(&mut self, expected: SuiTokenKind) -> Result<(), ParseError> {
        if std::mem::discriminant(&self.peek_kind()) == std::mem::discriminant(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: format!("{}", expected),
                found: format!("{}", self.peek_kind()),
                line: self.peek().span.line,
                column: self.peek().span.column,
            })
        }
    }

    fn expect_identifier(&mut self) -> Result<String, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::Identifier(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: format!("{}", self.peek_kind()),
                line: self.peek().span.line,
                column: self.peek().span.column,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> Result<SuiTemplate, ParseError> {
        let mut parser = SuiParser::new(source);
        parser.parse()
    }

    #[test]
    fn test_simple_component() {
        let source = r#"{@ component Counter @}
{$ let count: i32 $}
<div>{{ count }}</div>"#;

        let template = parse(source).unwrap();
        assert_eq!(template.kind, TemplateKind::Component);
        assert_eq!(template.name, "Counter");
        assert_eq!(template.declarations.len(), 1);
        assert_eq!(template.declarations[0].name, "count");
    }

    #[test]
    fn test_if_control() {
        let source = r#"{@ component Test @}
{% if x > 0: %}
<span>positive</span>
{% else: %}
<span>not positive</span>
{% end %}"#;

        let template = parse(source).unwrap();
        // Find the If control node (may have whitespace nodes before it)
        let if_node = template.content.iter().find_map(|n| {
            if let TemplateNode::Control(ControlNode::If(if_node)) = n {
                Some(if_node)
            } else {
                None
            }
        }).expect("Expected If control node");

        // Find span element in then branch
        let has_span_in_then = if_node.then_branch.iter().any(|n| {
            matches!(n, TemplateNode::Element(el) if el.tag == "span")
        });
        assert!(has_span_in_then, "Expected span in then branch");
        assert!(if_node.else_branch.is_some());
    }

    #[test]
    fn test_for_control() {
        let source = r#"{@ component Test @}
{% for item in items: %}
<li>{{ item.name }}</li>
{% end %}"#;

        let template = parse(source).unwrap();
        // Find the For control node
        let for_node = template.content.iter().find_map(|n| {
            if let TemplateNode::Control(ControlNode::For(for_node)) = n {
                Some(for_node)
            } else {
                None
            }
        }).expect("Expected For control node");
        assert_eq!(for_node.binding, "item");
    }

    #[test]
    fn test_element_with_attrs() {
        let source = r#"{@ component Test @}
<button id="btn" class="primary" disabled>Click</button>"#;

        let template = parse(source).unwrap();
        // Find the button element
        let button = template.content.iter().find_map(|n| {
            if let TemplateNode::Element(el) = n {
                if el.tag == "button" {
                    return Some(el);
                }
            }
            None
        }).expect("Expected button Element node");
        assert_eq!(button.tag, "button");
        assert_eq!(button.attrs.len(), 3);
    }

    #[test]
    fn test_server_block() {
        let source = r#"{@ page Home @}
{- count = 42 -}"#;

        let template = parse(source).unwrap();
        assert!(template.server_block.is_some());
        let server = template.server_block.unwrap();
        assert_eq!(server.statements.len(), 1);
    }

    #[test]
    fn test_client_block() {
        let source = r##"{@ component Counter @}
{+ on_click("#btn", handler) +}"##;

        let template = parse(source).unwrap();
        assert!(template.client_block.is_some());
    }

    #[test]
    fn test_embed() {
        let source = r#"{@ page Home @}
{@ embed UserList users=users hydrate="visible" @}"#;

        let template = parse(source).unwrap();
        // Find the embed node
        let embed = template.content.iter().find_map(|n| {
            if let TemplateNode::Embed(embed) = n {
                Some(embed)
            } else {
                None
            }
        }).expect("Expected Embed node");
        assert_eq!(embed.component, "UserList");
        assert_eq!(embed.hydrate, HydrateStrategy::Visible);
    }
}
