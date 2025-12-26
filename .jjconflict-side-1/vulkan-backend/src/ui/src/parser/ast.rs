//! AST types for SUI templates
//!
//! This module defines the abstract syntax tree for parsed `.sui` template files.

use crate::lexer::Span;

/// A complete SUI template (page, component, or layout)
#[derive(Debug, Clone, PartialEq)]
pub struct SuiTemplate {
    pub span: Span,
    pub kind: TemplateKind,
    pub name: String,
    pub layout: Option<String>,
    pub layout_props: Vec<(String, Expr)>,
    pub declarations: Vec<StateDecl>,
    pub server_block: Option<ServerBlock>,
    pub client_block: Option<ClientBlock>,
    pub content: Vec<TemplateNode>,
}

impl SuiTemplate {
    pub fn new(kind: TemplateKind, name: String) -> Self {
        Self {
            span: Span::default(),
            kind,
            name,
            layout: None,
            layout_props: Vec::new(),
            declarations: Vec::new(),
            server_block: None,
            client_block: None,
            content: Vec::new(),
        }
    }
}

/// Type of template file
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateKind {
    /// Root mount point for SSR
    Page,
    /// Reusable embedded component
    Component,
    /// Layout wrapper with slots
    Layout,
}

/// State declaration `{$ let name: Type $}`
#[derive(Debug, Clone, PartialEq)]
pub struct StateDecl {
    pub span: Span,
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub default: Option<Expr>,
}

/// Server-side initialization block `{- ... -}`
#[derive(Debug, Clone, PartialEq)]
pub struct ServerBlock {
    pub span: Span,
    pub statements: Vec<Statement>,
}

/// Client-side event handlers block `{+ ... +}`
#[derive(Debug, Clone, PartialEq)]
pub struct ClientBlock {
    pub span: Span,
    pub statements: Vec<Statement>,
}

/// A node in the template tree
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateNode {
    /// HTML element `<tag attr="value">children</tag>`
    Element(Element),
    /// Plain text content
    Text(TextNode),
    /// Output expression `{{ expr }}`
    Output(OutputNode),
    /// Raw (unescaped) output `{! expr !}`
    RawOutput(OutputNode),
    /// Control flow `{% if/for/let %}`
    Control(ControlNode),
    /// Embed component `{@ embed Component @}`
    Embed(EmbedNode),
    /// Slot definition `{@ slot name @}`
    Slot(SlotNode),
    /// Fill slot content `{@ fill name @}content{@ end @}`
    Fill(FillNode),
    /// Comment `{# ... #}`
    Comment(String),
}

/// HTML element node
#[derive(Debug, Clone, PartialEq)]
pub struct Element {
    pub span: Span,
    pub tag: String,
    pub attrs: Vec<Attribute>,
    pub children: Vec<TemplateNode>,
    pub self_closing: bool,
}

impl Element {
    pub fn new(tag: String) -> Self {
        Self {
            span: Span::default(),
            tag,
            attrs: Vec::new(),
            children: Vec::new(),
            self_closing: false,
        }
    }
}

/// HTML attribute
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
    pub span: Span,
    pub name: String,
    pub value: AttributeValue,
}

/// Attribute value types
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    /// Static string `attr="value"`
    Static(String),
    /// Dynamic expression `attr="{{ expr }}"`
    Dynamic(Expr),
    /// Boolean attribute (presence-based) `disabled`
    Boolean,
    /// Conditional class `class:name="{{ condition }}"`
    ConditionalClass { class: String, condition: Expr },
    /// Event handler `on:click="{{ handler }}"`
    Event { event: String, handler: Expr },
}

/// Text content node
#[derive(Debug, Clone, PartialEq)]
pub struct TextNode {
    pub span: Span,
    pub content: String,
}

/// Output expression node `{{ expr }}` or `{! expr !}`
#[derive(Debug, Clone, PartialEq)]
pub struct OutputNode {
    pub span: Span,
    pub expr: Expr,
}

/// Control flow node
#[derive(Debug, Clone, PartialEq)]
pub enum ControlNode {
    /// `{% if condition: %}...{% elif: %}...{% else: %}...{% end %}`
    If(IfNode),
    /// `{% for item in collection: %}...{% end %}`
    For(ForNode),
    /// `{% let name = expr %}`
    Let(LetNode),
}

/// If/elif/else control node
#[derive(Debug, Clone, PartialEq)]
pub struct IfNode {
    pub span: Span,
    pub condition: Expr,
    pub then_branch: Vec<TemplateNode>,
    pub elif_branches: Vec<(Expr, Vec<TemplateNode>)>,
    pub else_branch: Option<Vec<TemplateNode>>,
}

/// For loop control node
#[derive(Debug, Clone, PartialEq)]
pub struct ForNode {
    pub span: Span,
    pub binding: String,
    pub index_binding: Option<String>,
    pub iterable: Expr,
    pub key: Option<Expr>,
    pub body: Vec<TemplateNode>,
}

/// Let binding control node
#[derive(Debug, Clone, PartialEq)]
pub struct LetNode {
    pub span: Span,
    pub name: String,
    pub value: Expr,
}

/// Embed component node `{@ embed Component props @}`
#[derive(Debug, Clone, PartialEq)]
pub struct EmbedNode {
    pub span: Span,
    pub component: String,
    pub props: Vec<(String, Expr)>,
    pub hydrate: HydrateStrategy,
}

/// Hydration strategy for embedded components
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum HydrateStrategy {
    /// Hydrate immediately on page load
    #[default]
    Load,
    /// Hydrate when scrolled into viewport
    Visible,
    /// Hydrate during browser idle time
    Idle,
    /// Hydrate on first user interaction
    Interaction,
    /// Never hydrate (static only)
    None,
}

impl HydrateStrategy {
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "load" => Some(HydrateStrategy::Load),
            "visible" => Some(HydrateStrategy::Visible),
            "idle" => Some(HydrateStrategy::Idle),
            "interaction" => Some(HydrateStrategy::Interaction),
            "none" => Some(HydrateStrategy::None),
            _ => None,
        }
    }
}

/// Slot definition node `{@ slot name @}`
#[derive(Debug, Clone, PartialEq)]
pub struct SlotNode {
    pub span: Span,
    pub name: String,
    pub default: Option<Vec<TemplateNode>>,
}

/// Fill slot content node `{@ fill name @}...{@ end @}`
#[derive(Debug, Clone, PartialEq)]
pub struct FillNode {
    pub span: Span,
    pub name: String,
    pub content: Vec<TemplateNode>,
}

// ============================================================================
// Expressions
// ============================================================================

/// Expression in template
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Integer literal
    Integer(i64),
    /// Float literal
    Float(f64),
    /// String literal
    String(String),
    /// Boolean literal
    Bool(bool),
    /// Nil literal
    Nil,
    /// Identifier
    Identifier(String),
    /// Binary operation
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// Unary operation
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    /// Field access `expr.field`
    FieldAccess {
        receiver: Box<Expr>,
        field: String,
    },
    /// Index access `expr[index]`
    IndexAccess {
        receiver: Box<Expr>,
        index: Box<Expr>,
    },
    /// Method call `expr.method(args)`
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
    },
    /// Function call `func(args)`
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    /// Array literal `[a, b, c]`
    Array(Vec<Expr>),
    /// Tuple literal `(a, b, c)`
    Tuple(Vec<Expr>),
    /// Dictionary literal `{a: 1, b: 2}`
    Dict(Vec<(String, Expr)>),
    /// Ternary/conditional `condition ? then : else`
    Ternary {
        condition: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Lambda/closure `fn(args): expr` or `|args| expr`
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
    },
    /// Range `start..end` or `start..=end`
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Comparison
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    // Logical
    And,
    Or,
    // String
    Concat,
}

impl BinOp {
    pub fn precedence(&self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::NotEq => 3,
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => 4,
            BinOp::Add | BinOp::Sub | BinOp::Concat => 5,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 6,
        }
    }
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

// ============================================================================
// Statements (for server/client blocks)
// ============================================================================

/// Statement in server/client blocks
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Variable assignment `name = expr`
    Assignment {
        target: String,
        value: Expr,
    },
    /// Let binding `let name = expr`
    Let {
        name: String,
        ty: Option<TypeExpr>,
        value: Expr,
    },
    /// Expression statement
    Expr(Expr),
    /// If statement
    If {
        condition: Expr,
        then_block: Vec<Statement>,
        else_block: Option<Vec<Statement>>,
    },
    /// For loop
    For {
        binding: String,
        iterable: Expr,
        body: Vec<Statement>,
    },
    /// While loop
    While {
        condition: Expr,
        body: Vec<Statement>,
    },
    /// Return statement
    Return(Option<Expr>),
    /// Break statement
    Break,
    /// Continue statement
    Continue,
}

// ============================================================================
// Types
// ============================================================================

/// Type expression
#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// Named type `i32`, `String`, `User`
    Named(String),
    /// Generic type `List[T]`, `Dict[K, V]`
    Generic {
        name: String,
        args: Vec<TypeExpr>,
    },
    /// Array type `[T]`
    Array(Box<TypeExpr>),
    /// Tuple type `(T, U, V)`
    Tuple(Vec<TypeExpr>),
    /// Optional type `T?`
    Optional(Box<TypeExpr>),
    /// Function type `fn(T, U) -> V`
    Function {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
    },
}
