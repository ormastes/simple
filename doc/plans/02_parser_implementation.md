# Parser Implementation Plan

## Overview

Implement the Simple language parser using Tree-sitter with Rust bindings. This provides fast, incremental parsing suitable for both compilation and IDE integration.

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Simple Compiler                       │
├─────────────────────────────────────────────────────────┤
│  Source File (.simple)                                   │
│         │                                                │
│         ▼                                                │
│  ┌─────────────────┐                                     │
│  │  Tree-sitter    │  grammar.js + scanner.c             │
│  │  Parser         │  (GLR parsing, indentation)         │
│  └────────┬────────┘                                     │
│           │                                              │
│           ▼                                              │
│  ┌─────────────────┐                                     │
│  │  Concrete       │  Tree-sitter Tree                   │
│  │  Syntax Tree    │  (with source positions)            │
│  └────────┬────────┘                                     │
│           │                                              │
│           ▼                                              │
│  ┌─────────────────┐                                     │
│  │  AST Builder    │  Rust: CST -> AST conversion        │
│  │  (Rust)         │                                     │
│  └────────┬────────┘                                     │
│           │                                              │
│           ▼                                              │
│  ┌─────────────────┐                                     │
│  │  Abstract       │  Typed Rust structs                 │
│  │  Syntax Tree    │                                     │
│  └─────────────────┘                                     │
└─────────────────────────────────────────────────────────┘
```

---

## Tasks

### Task 1: Project Setup

**Files to create:**
```
simple-compiler/
├── Cargo.toml
├── tree-sitter-simple/
│   ├── Cargo.toml
│   ├── grammar.js
│   ├── src/
│   │   ├── scanner.c
│   │   └── lib.rs
│   ├── queries/
│   │   └── highlights.scm
│   └── build.rs
└── crates/
    └── parser/
        ├── Cargo.toml
        └── src/
            ├── lib.rs
            ├── ast.rs
            ├── builder.rs
            └── error.rs
```

**Cargo.toml (workspace root):**
```toml
[workspace]
members = [
    "tree-sitter-simple",
    "crates/parser",
]

[workspace.dependencies]
tree-sitter = "0.22"
thiserror = "1.0"
```

---

### Task 2: Tree-sitter Grammar (grammar.js)

Implement the complete grammar from `simple_lexer_parser_spec.md`:

**Priority order:**
1. Basic expressions (literals, identifiers, operators)
2. Statements (let, if, for, while, return)
3. Functions (fn definition, parameters, calls)
4. Types (simple types, generics, pointers)
5. Structs and Classes
6. Enums and Pattern Matching
7. Traits and Impl blocks
8. Actors and Concurrency
9. Macros

**Key grammar rules (subset):**
```javascript
module.exports = grammar({
  name: 'simple',

  externals: $ => [
    $._indent,
    $._dedent,
    $._newline,
  ],

  rules: {
    source_file: $ => repeat($._definition),

    _definition: $ => choice(
      $.function_definition,
      $.struct_definition,
      // ... more
    ),

    function_definition: $ => seq(
      optional('pub'),
      'fn',
      $.identifier,
      $.parameters,
      optional(seq('->', $.type)),
      ':',
      $.block,
    ),

    // ... rest of grammar
  },
});
```

---

### Task 3: External Scanner (scanner.c)

Handle indentation-sensitive parsing:

```c
enum TokenType {
    INDENT,
    DEDENT,
    NEWLINE,
};

typedef struct {
    uint16_t indent_stack[MAX_DEPTH];
    uint8_t  indent_depth;
} Scanner;

bool tree_sitter_simple_external_scanner_scan(
    void *payload,
    TSLexer *lexer,
    const bool *valid_symbols
) {
    Scanner *scanner = payload;

    // Handle newlines and indentation changes
    if (lexer->lookahead == '\n') {
        // ... count next line's indentation
        // ... emit INDENT, DEDENT, or NEWLINE
    }

    return false;
}
```

---

### Task 4: Rust AST Definitions (ast.rs)

Define typed AST nodes:

```rust
// ast.rs

use std::ops::Range;

/// Source location
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

/// All AST nodes
#[derive(Debug, Clone)]
pub enum Node {
    // Definitions
    Function(FunctionDef),
    Struct(StructDef),
    Class(ClassDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplBlock),
    Actor(ActorDef),

    // Statements
    Let(LetStmt),
    Return(ReturnStmt),
    If(IfStmt),
    Match(MatchStmt),
    For(ForStmt),
    While(WhileStmt),
    Expression(Expr),

    // Expressions
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    pub body: Block,
    pub is_public: bool,
    pub effect: Option<Effect>,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub default: Option<Expr>,
    pub is_mutable: bool,
}

#[derive(Debug, Clone)]
pub enum Type {
    Simple(String),
    Generic { name: String, args: Vec<Type> },
    Pointer { kind: PointerKind, inner: Box<Type> },
    Tuple(Vec<Type>),
    Array { element: Box<Type>, size: Option<Box<Expr>> },
    Function { params: Vec<Type>, ret: Option<Box<Type>> },
    Union(Vec<Type>),
    Optional(Box<Type>),
}

#[derive(Debug, Clone, Copy)]
pub enum PointerKind {
    Unique,   // &T
    Shared,   // *T
    Weak,     // -T
    Handle,   // +T
}

#[derive(Debug, Clone)]
pub enum Expr {
    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,
    Symbol(String),

    // Compound
    Identifier(String),
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr> },
    Unary { op: UnaryOp, operand: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Argument> },
    MethodCall { receiver: Box<Expr>, method: String, args: Vec<Argument> },
    FieldAccess { receiver: Box<Expr>, field: String },
    Index { receiver: Box<Expr>, index: Box<Expr> },
    Lambda { params: Vec<LambdaParam>, body: Box<Expr> },
    If { condition: Box<Expr>, then_branch: Box<Expr>, else_branch: Option<Box<Expr>> },
    Match { subject: Box<Expr>, arms: Vec<MatchArm> },
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Struct { name: String, fields: Vec<(String, Expr)> },
    Spawn(Box<Expr>),
    New { kind: PointerKind, ty: String, args: Vec<Argument> },
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,
    Identifier(String),
    Literal(Expr),
    Tuple(Vec<Pattern>),
    Struct { name: String, fields: Vec<(String, Pattern)> },
    Enum { name: String, payload: Option<Vec<Pattern>> },
    Or(Vec<Pattern>),
    Typed { pattern: Box<Pattern>, ty: Type },
}

// ... more definitions
```

---

### Task 5: AST Builder (builder.rs)

Convert Tree-sitter CST to typed AST:

```rust
// builder.rs

use tree_sitter::{Node, Tree};
use crate::ast::*;
use crate::error::ParseError;

pub struct AstBuilder<'a> {
    source: &'a str,
}

impl<'a> AstBuilder<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source }
    }

    pub fn build(&self, tree: &Tree) -> Result<Vec<Node>, ParseError> {
        let root = tree.root_node();
        self.build_source_file(root)
    }

    fn build_source_file(&self, node: Node) -> Result<Vec<Node>, ParseError> {
        let mut definitions = Vec::new();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "function_definition" => {
                    definitions.push(Node::Function(self.build_function(child)?));
                }
                "struct_definition" => {
                    definitions.push(Node::Struct(self.build_struct(child)?));
                }
                // ... more kinds
                _ => {}
            }
        }

        Ok(definitions)
    }

    fn build_function(&self, node: Node) -> Result<FunctionDef, ParseError> {
        let mut name = String::new();
        let mut params = Vec::new();
        let mut return_type = None;
        let mut body = Block::default();
        let mut is_public = false;
        let mut effect = None;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "pub" => is_public = true,
                "identifier" => name = self.text(child).to_string(),
                "parameters" => params = self.build_parameters(child)?,
                "type" => return_type = Some(self.build_type(child)?),
                "effect_modifier" => effect = Some(self.build_effect(child)?),
                "block" => body = self.build_block(child)?,
                _ => {}
            }
        }

        Ok(FunctionDef {
            span: self.span(node),
            name,
            params,
            return_type,
            body,
            is_public,
            effect,
        })
    }

    fn build_expression(&self, node: Node) -> Result<Expr, ParseError> {
        match node.kind() {
            "integer" => {
                let text = self.text(node);
                let value = parse_integer(text)?;
                Ok(Expr::Integer(value))
            }
            "float" => {
                let text = self.text(node);
                let value: f64 = text.parse()?;
                Ok(Expr::Float(value))
            }
            "string" => {
                let text = self.text(node);
                Ok(Expr::String(parse_string(text)?))
            }
            "identifier" => {
                Ok(Expr::Identifier(self.text(node).to_string()))
            }
            "binary_expression" => {
                self.build_binary_expr(node)
            }
            "call_expression" => {
                self.build_call_expr(node)
            }
            // ... more expression types
            _ => Err(ParseError::UnknownNode(node.kind().to_string())),
        }
    }

    fn text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    fn span(&self, node: Node) -> Span {
        let start = node.start_position();
        Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: start.row + 1,
            column: start.column + 1,
        }
    }
}
```

---

### Task 6: Error Handling (error.rs)

```rust
// error.rs

use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Syntax error at {line}:{column}: {message}")]
    SyntaxError {
        message: String,
        line: usize,
        column: usize,
    },

    #[error("Unknown node type: {0}")]
    UnknownNode(String),

    #[error("Expected {expected}, found {found}")]
    Expected {
        expected: String,
        found: String,
    },

    #[error("Invalid integer literal: {0}")]
    InvalidInteger(String),

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String),

    #[error("Unclosed string literal")]
    UnclosedString,
}

pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub span: Option<Span>,
    pub notes: Vec<String>,
}

pub enum DiagnosticLevel {
    Error,
    Warning,
    Info,
}
```

---

### Task 7: Parser Public API (lib.rs)

```rust
// crates/parser/src/lib.rs

mod ast;
mod builder;
mod error;

pub use ast::*;
pub use error::*;

use tree_sitter::Parser;

pub struct SimpleParser {
    parser: Parser,
}

impl SimpleParser {
    pub fn new() -> Result<Self, ParseError> {
        let mut parser = Parser::new();
        parser
            .set_language(tree_sitter_simple::language())
            .map_err(|e| ParseError::SyntaxError {
                message: e.to_string(),
                line: 0,
                column: 0,
            })?;

        Ok(Self { parser })
    }

    /// Parse source code into AST
    pub fn parse(&mut self, source: &str) -> Result<Module, ParseError> {
        let tree = self.parser
            .parse(source, None)
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Parser returned no tree".into(),
                line: 0,
                column: 0,
            })?;

        if tree.root_node().has_error() {
            return Err(self.collect_errors(&tree, source));
        }

        let builder = builder::AstBuilder::new(source);
        let definitions = builder.build(&tree)?;

        Ok(Module {
            source: source.to_string(),
            definitions,
        })
    }

    /// Parse with incremental update
    pub fn parse_incremental(
        &mut self,
        source: &str,
        old_tree: Option<&tree_sitter::Tree>,
    ) -> Result<Module, ParseError> {
        let tree = self.parser
            .parse(source, old_tree)
            .ok_or_else(|| ParseError::SyntaxError {
                message: "Parser returned no tree".into(),
                line: 0,
                column: 0,
            })?;

        let builder = builder::AstBuilder::new(source);
        let definitions = builder.build(&tree)?;

        Ok(Module {
            source: source.to_string(),
            definitions,
        })
    }

    fn collect_errors(&self, tree: &tree_sitter::Tree, source: &str) -> ParseError {
        // Walk tree and collect all ERROR nodes
        // Return first error for now
        ParseError::SyntaxError {
            message: "Syntax error in source".into(),
            line: 1,
            column: 1,
        }
    }
}

#[derive(Debug)]
pub struct Module {
    pub source: String,
    pub definitions: Vec<Node>,
}
```

---

## Testing Plan

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_function() {
        let mut parser = SimpleParser::new().unwrap();
        let source = r#"
fn add(a: i64, b: i64) -> i64:
    return a + b
"#;
        let module = parser.parse(source).unwrap();
        assert_eq!(module.definitions.len(), 1);
    }

    #[test]
    fn test_parse_struct() {
        let mut parser = SimpleParser::new().unwrap();
        let source = r#"
struct Point:
    x: i64
    y: i64
"#;
        let module = parser.parse(source).unwrap();
        assert_eq!(module.definitions.len(), 1);
    }

    // ... more tests
}
```

### Integration Tests

Create `tests/fixtures/` with `.simple` files and expected AST JSON.

---

## Implementation Order

1. **Week 1**: Project setup, basic grammar (literals, identifiers)
2. **Week 2**: Expressions (binary, unary, calls)
3. **Week 3**: Statements (let, if, for, while, return)
4. **Week 4**: Functions, indentation handling
5. **Week 5**: Types, structs, classes
6. **Week 6**: Enums, pattern matching
7. **Week 7**: Traits, impl blocks
8. **Week 8**: Actors, concurrency syntax

---

## Dependencies

```toml
[dependencies]
tree-sitter = "0.22"
thiserror = "1.0"

[dev-dependencies]
pretty_assertions = "1.4"
```
