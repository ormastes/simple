# Simple Language Parser Integration and Queries

Part of [Lexer and Parser Specification](lexer_parser.md).

## Parser Integration Module (`src/parser.rs`)

```rust
//! High-level parser interface for Simple language
//!
//! Provides a convenient API for parsing Simple source code and
//! working with the resulting syntax tree.

use std::collections::HashMap;
use tree_sitter::{Language, Node, Parser, Query, QueryCursor, Tree};

/// A parsed Simple source file.
pub struct ParsedSource {
    pub tree: Tree,
    pub source: String,
}

/// Simple language parser with caching and error recovery.
pub struct SimpleParser {
    parser: Parser,
    query_cache: HashMap<String, Query>,
}

impl SimpleParser {
    /// Create a new Simple parser.
    pub fn new() -> Result<Self, String> {
        let mut parser = Parser::new();
        parser
            .set_language(crate::language())
            .map_err(|e| format!("Failed to set language: {}", e))?;

        Ok(Self {
            parser,
            query_cache: HashMap::new(),
        })
    }

    /// Parse a Simple source file.
    pub fn parse(&mut self, source: &str) -> Result<ParsedSource, ParseError> {
        let tree = self.parser
            .parse(source, None)
            .ok_or(ParseError::ParserError)?;

        if tree.root_node().has_error() {
            let errors = self.collect_errors(&tree, source);
            return Err(ParseError::SyntaxErrors(errors));
        }

        Ok(ParsedSource {
            tree,
            source: source.to_string(),
        })
    }

    /// Parse with incremental update from previous tree.
    pub fn parse_incremental(
        &mut self,
        source: &str,
        old_tree: Option<&Tree>,
    ) -> Result<ParsedSource, ParseError> {
        let tree = self.parser
            .parse(source, old_tree)
            .ok_or(ParseError::ParserError)?;

        if tree.root_node().has_error() {
            let errors = self.collect_errors(&tree, source);
            return Err(ParseError::SyntaxErrors(errors));
        }

        Ok(ParsedSource {
            tree,
            source: source.to_string(),
        })
    }

    /// Collect all syntax errors from the tree.
    fn collect_errors(&self, tree: &Tree, source: &str) -> Vec<SyntaxError> {
        let mut errors = Vec::new();
        let mut cursor = tree.walk();

        self.collect_errors_recursive(&mut cursor, source, &mut errors);
        errors
    }

    fn collect_errors_recursive(
        &self,
        cursor: &mut tree_sitter::TreeCursor,
        source: &str,
        errors: &mut Vec<SyntaxError>,
    ) {
        let node = cursor.node();

        if node.is_error() {
            let start = node.start_position();
            let end = node.end_position();
            let text = &source[node.byte_range()];

            errors.push(SyntaxError {
                message: format!("Unexpected token: {}", text.chars().take(20).collect::<String>()),
                line: start.row + 1,
                column: start.column + 1,
                end_line: end.row + 1,
                end_column: end.column + 1,
            });
        } else if node.is_missing() {
            let pos = node.start_position();
            errors.push(SyntaxError {
                message: format!("Missing {}", node.kind()),
                line: pos.row + 1,
                column: pos.column + 1,
                end_line: pos.row + 1,
                end_column: pos.column + 1,
            });
        }

        if cursor.goto_first_child() {
            loop {
                self.collect_errors_recursive(cursor, source, errors);
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            cursor.goto_parent();
        }
    }

    /// Execute a query on the syntax tree.
    pub fn query(
        &mut self,
        parsed: &ParsedSource,
        query_source: &str,
    ) -> Result<Vec<QueryMatch>, String> {
        let query = self.get_or_create_query(query_source)?;
        let mut cursor = QueryCursor::new();

        let matches: Vec<QueryMatch> = cursor
            .matches(&query, parsed.tree.root_node(), parsed.source.as_bytes())
            .map(|m| QueryMatch {
                pattern_index: m.pattern_index,
                captures: m.captures
                    .iter()
                    .map(|c| Capture {
                        name: query.capture_names()[c.index as usize].to_string(),
                        node_kind: c.node.kind().to_string(),
                        text: parsed.source[c.node.byte_range()].to_string(),
                        start: Position {
                            line: c.node.start_position().row + 1,
                            column: c.node.start_position().column + 1,
                        },
                        end: Position {
                            line: c.node.end_position().row + 1,
                            column: c.node.end_position().column + 1,
                        },
                    })
                    .collect(),
            })
            .collect();

        Ok(matches)
    }

    fn get_or_create_query(&mut self, source: &str) -> Result<Query, String> {
        if let Some(query) = self.query_cache.get(source) {
            return Ok(query.clone());
        }

        let query = Query::new(crate::language(), source)
            .map_err(|e| format!("Query error: {:?}", e))?;

        self.query_cache.insert(source.to_string(), query.clone());
        Ok(query)
    }
}

impl Default for SimpleParser {
    fn default() -> Self {
        Self::new().expect("Failed to create parser")
    }
}

/// Parse error types.
#[derive(Debug, Clone)]
pub enum ParseError {
    ParserError,
    SyntaxErrors(Vec<SyntaxError>),
}

/// A syntax error in the source.
#[derive(Debug, Clone)]
pub struct SyntaxError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub end_line: usize,
    pub end_column: usize,
}

impl std::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

/// A query match result.
#[derive(Debug, Clone)]
pub struct QueryMatch {
    pub pattern_index: usize,
    pub captures: Vec<Capture>,
}

/// A captured node from a query.
#[derive(Debug, Clone)]
pub struct Capture {
    pub name: String,
    pub node_kind: String,
    pub text: String,
    pub start: Position,
    pub end: Position,
}

/// A position in the source.
#[derive(Debug, Clone, Copy)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}
```

---

## AST Visitor Module (`src/visitor.rs`)

```rust
//! AST visitor pattern for Simple language syntax trees
//!
//! Provides traits and utilities for traversing and transforming
//! parsed Simple code.

use tree_sitter::Node;

/// Trait for visiting Simple AST nodes.
pub trait Visitor {
    /// Visit a source file (root node).
    fn visit_source_file(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a function definition.
    fn visit_function_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a struct definition.
    fn visit_struct_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a class definition.
    fn visit_class_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit an enum definition.
    fn visit_enum_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a trait definition.
    fn visit_trait_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit an impl block.
    fn visit_impl_block(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit an actor definition.
    fn visit_actor_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a handle pool definition.
    fn visit_handle_pool_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a macro definition.
    fn visit_macro_definition(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit an expression.
    fn visit_expression(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a statement.
    fn visit_statement(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a pattern.
    fn visit_pattern(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit a type.
    fn visit_type(&mut self, node: Node, source: &str) {
        self.visit_children(node, source);
    }

    /// Visit an identifier.
    fn visit_identifier(&mut self, _node: Node, _source: &str) {}

    /// Visit a literal.
    fn visit_literal(&mut self, _node: Node, _source: &str) {}

    /// Default child visitor.
    fn visit_children(&mut self, node: Node, source: &str) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.visit(child, source);
        }
    }

    /// Main dispatch method.
    fn visit(&mut self, node: Node, source: &str) {
        match node.kind() {
            "source_file" => self.visit_source_file(node, source),
            "function_definition" => self.visit_function_definition(node, source),
            "struct_definition" => self.visit_struct_definition(node, source),
            "class_definition" => self.visit_class_definition(node, source),
            "enum_definition" => self.visit_enum_definition(node, source),
            "trait_definition" => self.visit_trait_definition(node, source),
            "impl_block" => self.visit_impl_block(node, source),
            "actor_definition" => self.visit_actor_definition(node, source),
            "handle_pool_definition" => self.visit_handle_pool_definition(node, source),
            "macro_definition" => self.visit_macro_definition(node, source),
            "identifier" | "type_identifier" => self.visit_identifier(node, source),
            "integer" | "float" | "string" | "boolean" | "nil" | "symbol" => {
                self.visit_literal(node, source)
            }
            kind if kind.ends_with("_expression") => self.visit_expression(node, source),
            kind if kind.ends_with("_statement") => self.visit_statement(node, source),
            kind if kind.ends_with("_pattern") => self.visit_pattern(node, source),
            kind if kind.ends_with("_type") || kind == "type" => self.visit_type(node, source),
            _ => self.visit_children(node, source),
        }
    }
}

/// Walk the AST with a visitor.
pub fn walk<V: Visitor>(visitor: &mut V, node: Node, source: &str) {
    visitor.visit(node, source);
}

/// Example: Collect all function names
pub struct FunctionCollector {
    pub functions: Vec<FunctionInfo>,
}

pub struct FunctionInfo {
    pub name: String,
    pub is_async: bool,
    pub line: usize,
}

impl FunctionCollector {
    pub fn new() -> Self {
        Self { functions: Vec::new() }
    }
}

impl Visitor for FunctionCollector {
    fn visit_function_definition(&mut self, node: Node, source: &str) {
        let mut name = String::new();
        let mut is_async = false;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    name = source[child.byte_range()].to_string();
                }
                "effect_modifier" => {
                    is_async = source[child.byte_range()] == *"async";
                }
                _ => {}
            }
        }

        if !name.is_empty() {
            self.functions.push(FunctionInfo {
                name,
                is_async,
                line: node.start_position().row + 1,
            });
        }

        self.visit_children(node, source);
    }
}

/// Example: Collect all handle pool types
pub struct HandlePoolCollector {
    pub pools: Vec<HandlePoolInfo>,
}

pub struct HandlePoolInfo {
    pub type_name: String,
    pub capacity: Option<u64>,
    pub line: usize,
}

impl HandlePoolCollector {
    pub fn new() -> Self {
        Self { pools: Vec::new() }
    }
}

impl Visitor for HandlePoolCollector {
    fn visit_handle_pool_definition(&mut self, node: Node, source: &str) {
        let mut type_name = String::new();
        let mut capacity = None;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "type_identifier" => {
                    type_name = source[child.byte_range()].to_string();
                }
                "pool_option" => {
                    // Parse capacity: value pairs
                    let mut opt_cursor = child.walk();
                    let mut key = String::new();
                    for opt_child in child.children(&mut opt_cursor) {
                        match opt_child.kind() {
                            "identifier" => {
                                key = source[opt_child.byte_range()].to_string();
                            }
                            "integer" if key == "capacity" => {
                                if let Ok(val) = source[opt_child.byte_range()].parse() {
                                    capacity = Some(val);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }

        if !type_name.is_empty() {
            self.pools.push(HandlePoolInfo {
                type_name,
                capacity,
                line: node.start_position().row + 1,
            });
        }
    }
}
```

---

## Syntax Highlighting Queries (`queries/highlights.scm`)

```scheme
; highlights.scm - Syntax highlighting for Simple language

; Keywords
[
  "struct" "class" "enum" "trait" "actor" "impl"
  "fn" "let" "mut" "immut" "type"
  "if" "else" "elif" "match" "case"
  "for" "while" "loop" "break" "continue" "return"
  "spawn" "send" "receive" "on" "state"
  "async" "async" "await"
  "new" "move"
  "context" "macro" "handle_pool" "gen_code"
  "pub" "priv" "extern" "static" "const" "global"
  "where" "as" "in" "is"
  ; Module system keywords
  "mod" "use" "export" "common" "auto" "import" "crate"
] @keyword

; Operators
[
  "and" "or" "not"
] @keyword.operator

; Boolean literals
[
  "true" "false"
] @boolean

; Nil literal
"nil" @constant.builtin

; Self
"self" @variable.builtin
"Self" @type.builtin

; Types
(type_identifier) @type
(simple_type) @type

; Pointer type prefixes
(pointer_type
  ["&" "*" "-" "+"] @type.qualifier)

; Functions
(function_definition
  name: (identifier) @function)

(method_definition
  name: (identifier) @function.method)

(call_expression
  function: (identifier) @function.call)

(method_call_expression
  method: (identifier) @function.method.call)

; Parameters
(parameter
  name: (identifier) @variable.parameter)

(lambda_param) @variable.parameter
(typed_lambda_param
  name: (identifier) @variable.parameter)

; Variables
(identifier) @variable

; Fields
(field_definition
  name: (identifier) @property)

(field_access
  field: (identifier) @property)

(field_argument
  name: (identifier) @property)

; Struct/Class names
(struct_definition
  name: (type_identifier) @type.definition)

(class_definition
  name: (type_identifier) @type.definition)

; Enum
(enum_definition
  name: (type_identifier) @type.definition)

(enum_variant
  name: (type_identifier) @constructor)

; Trait
(trait_definition
  name: (type_identifier) @type.definition)

; Actor
(actor_definition
  name: (type_identifier) @type.definition)

(message_handler
  message: (type_identifier) @constructor)

; Handle pool
(handle_pool_definition
  type: (type_identifier) @type.definition)

; Literals
(integer) @number
(float) @number.float
(string) @string
(char) @character
(symbol) @symbol

; String interpolation
(interpolation
  "{" @punctuation.special
  "}" @punctuation.special)

(escape_sequence) @string.escape

; Comments
(comment) @comment

; Operators
[
  "+" "-" "*" "/" "%" "**"
  "==" "!=" "<" ">" "<=" ">="
  "=" "->" "<-"
  "&&" "||" "!"
  "&" "|" "^" "~" "<<" ">>"
] @operator

; Punctuation
[ "(" ")" "[" "]" "{" "}" ] @punctuation.bracket
[ ":" ";" "," "." ".." "..." "@" "#" "\\" "?" ] @punctuation.delimiter

; Effect modifiers
(effect_modifier) @attribute

; Macros
(macro_definition
  name: (identifier) @function.macro)
```

---

## Local Variables Queries (`queries/locals.scm`)

```scheme
; locals.scm - Scope and reference tracking for Simple

; Scopes
(source_file) @scope
(function_definition) @scope
(method_definition) @scope
(block) @scope
(lambda_expression) @scope
(for_statement) @scope
(match_statement) @scope
(case_clause) @scope
(actor_definition) @scope
(message_handler) @scope

; Definitions
(function_definition
  name: (identifier) @definition.function)

(method_definition
  name: (identifier) @definition.method)

(struct_definition
  name: (type_identifier) @definition.type)

(class_definition
  name: (type_identifier) @definition.type)

(enum_definition
  name: (type_identifier) @definition.type)

(trait_definition
  name: (type_identifier) @definition.type)

(actor_definition
  name: (type_identifier) @definition.type)

(handle_pool_definition
  type: (type_identifier) @definition.type)

(let_statement
  pattern: (identifier_pattern) @definition.var)

(parameter
  name: (identifier) @definition.parameter)

(lambda_param) @definition.parameter

(typed_lambda_param
  name: (identifier) @definition.parameter)

(for_statement
  pattern: (identifier_pattern) @definition.var)

(field_definition
  name: (identifier) @definition.field)

; References
(identifier) @reference
(type_identifier) @reference
```

---

## Indentation Queries (`queries/indents.scm`)

```scheme
; indents.scm - Automatic indentation rules for Simple

; Indent after these nodes
[
  (function_definition)
  (method_definition)
  (struct_definition)
  (class_definition)
  (enum_definition)
  (trait_definition)
  (impl_block)
  (actor_definition)
  (handle_pool_definition)
  (macro_definition)
  (if_statement)
  (elif_clause)
  (else_clause)
  (for_statement)
  (while_statement)
  (loop_statement)
  (match_statement)
  (case_clause)
  (receive_block)
  (context_block)
  (state_block)
  (message_handler)
] @indent

; Dedent at block end
(block) @dedent

; Align case clauses
(case_clause) @aligned_indent
```

---

## Example Usage

### Basic Parsing

```rust
use tree_sitter_simple::{language, SimpleParser};

fn main() {
    let mut parser = SimpleParser::new().unwrap();

    let source = r#"
struct Point:
    x: f64
    y: f64

fn distance(p1: Point, p2: Point) -> f64:
    let dx = p2.x - p1.x
    let dy = p2.y - p1.y
    return sqrt(dx * dx + dy * dy)

actor GameWorld:
    state:
        players: List[+Player] = []

    on Tick(dt: f64) async:
        for handle in self.players:
            match Player.handle_get_mut(handle):
                case Some(player):
                    player.update(dt)
                case None:
                    pass
"#;

    match parser.parse(source) {
        Ok(parsed) => {
            println!("Parse successful!");
            println!("Root node: {}", parsed.tree.root_node().to_sexp());
        }
        Err(e) => {
            eprintln!("Parse error: {:?}", e);
        }
    }
}
```

### Function Extraction

```rust
use tree_sitter_simple::{SimpleParser, visitor::{FunctionCollector, walk}};

fn main() {
    let mut parser = SimpleParser::new().unwrap();

    let source = r#"
fn regular_function(x: i64) -> i64:
    return x * 2

fn async_operation() async -> Result[Data]:
    let data = await fetch_data()
    return data

actor Counter:
    state:
        value: i64 = 0

    on Inc(by: i64) async:
        self.value = self.value + by
"#;

    let parsed = parser.parse(source).unwrap();

    let mut collector = FunctionCollector::new();
    walk(&mut collector, parsed.tree.root_node(), &parsed.source);

    for func in &collector.functions {
        println!(
            "Function '{}' at line {} (async: {})",
            func.name, func.line, func.is_async
        );
    }
}
```

### Handle Pool Analysis

```rust
use tree_sitter_simple::{SimpleParser, visitor::{HandlePoolCollector, walk}};

fn main() {
    let mut parser = SimpleParser::new().unwrap();

    let source = r#"
handle_pool Enemy:
    capacity: 10000

handle_pool Projectile:
    capacity: 50000

handle_pool Particle:
    capacity: 100000
"#;

    let parsed = parser.parse(source).unwrap();

    let mut collector = HandlePoolCollector::new();
    walk(&mut collector, parsed.tree.root_node(), &parsed.source);

    for pool in &collector.pools {
        println!(
            "Handle pool for '{}' at line {} with capacity {:?}",
            pool.type_name, pool.line, pool.capacity
        );
    }
}
```

---

## GLR Parsing Notes

### Why GLR?

Tree-sitter uses GLR (Generalized LR) parsing to handle:

1. **Ambiguous grammar constructs** - Simple has several points where the grammar is locally ambiguous:
   - Type expressions vs comparison expressions (`List[T]` vs `a[b]`)
   - Lambda expressions vs other constructs
   - Struct literals vs blocks

2. **Fast error recovery** - GLR maintains multiple parse states, allowing quick recovery from syntax errors while still producing useful partial parse trees.

3. **Incremental parsing** - The GLR algorithm enables efficient re-parsing of edited files by reusing unchanged subtrees.

### Conflict Resolution

The grammar uses several mechanisms to resolve GLR conflicts:

1. **Precedence declarations** - Explicit precedence levels for operators and constructs
2. **Associativity** - Left/right associativity for binary operators
3. **Inline rules** - Certain rules are inlined to reduce parser states
4. **Conflict declarations** - Explicit listing of acceptable conflicts with automatic resolution

### Performance Characteristics

| Metric | Typical Value |
|--------|---------------|
| Parse throughput | ~10 MB/s on modern hardware |
| Memory per tree | O(n) where n = source size |
| Incremental re-parse | O(log n + changed region) |
| Query time | O(matches) |

---

## File Structure

```
tree-sitter-simple/
├── Cargo.toml
├── build.rs
├── grammar.js
├── src/
│   ├── lib.rs
│   ├── parser.rs
│   ├── visitor.rs
│   ├── parser.c          (generated)
│   ├── scanner.c
│   └── node-types.json   (generated)
├── queries/
│   ├── highlights.scm
│   ├── locals.scm
│   ├── indents.scm
│   └── injections.scm
└── test/
    ├── corpus/
    │   ├── definitions.txt
    │   ├── expressions.txt
    │   ├── statements.txt
    │   ├── patterns.txt
    │   ├── actors.txt
    │   └── memory.txt
    └── highlight/
        └── sample.simple
```

---

## Building and Testing

```bash
# Generate parser from grammar.js
npx tree-sitter generate

# Build Rust library
cargo build --release

# Run tests
cargo test

# Run Tree-sitter tests
npx tree-sitter test

# Parse a file
npx tree-sitter parse example.simple

# Generate highlighting
npx tree-sitter highlight example.simple
```

---

Back to: [Lexer and Parser Specification](lexer_parser.md)
