# Simple Language External Scanner and Rust Bindings

Part of [Lexer and Parser Specification](lexer_parser.md).

## External Scanner (`scanner.c`)

The external scanner handles context-sensitive tokens like INDENT, DEDENT, and NEWLINE.

```c
// scanner.c - External scanner for Simple language
// Handles indentation-sensitive parsing

#include <tree_sitter/parser.h>
#include <wctype.h>
#include <string.h>

enum TokenType {
    INDENT,
    DEDENT,
    NEWLINE,
    STRING_START,
    STRING_CONTENT,
    STRING_END,
};

#define MAX_INDENT_DEPTH 100

typedef struct {
    uint16_t indent_stack[MAX_INDENT_DEPTH];
    uint8_t indent_depth;
    bool inside_string;
    char string_delimiter;
    uint8_t pending_dedents;
} Scanner;

// Initialize scanner state
void *tree_sitter_simple_external_scanner_create() {
    Scanner *scanner = calloc(1, sizeof(Scanner));
    scanner->indent_stack[0] = 0;
    scanner->indent_depth = 1;
    return scanner;
}

void tree_sitter_simple_external_scanner_destroy(void *payload) {
    free(payload);
}

// Serialize scanner state
unsigned tree_sitter_simple_external_scanner_serialize(
    void *payload,
    char *buffer
) {
    Scanner *scanner = payload;
    size_t size = 0;

    buffer[size++] = scanner->indent_depth;
    buffer[size++] = scanner->inside_string;
    buffer[size++] = scanner->string_delimiter;
    buffer[size++] = scanner->pending_dedents;

    for (uint8_t i = 0; i < scanner->indent_depth; i++) {
        buffer[size++] = scanner->indent_stack[i] & 0xFF;
        buffer[size++] = (scanner->indent_stack[i] >> 8) & 0xFF;
    }

    return size;
}

// Deserialize scanner state
void tree_sitter_simple_external_scanner_deserialize(
    void *payload,
    const char *buffer,
    unsigned length
) {
    Scanner *scanner = payload;

    if (length == 0) {
        scanner->indent_stack[0] = 0;
        scanner->indent_depth = 1;
        scanner->inside_string = false;
        scanner->string_delimiter = 0;
        scanner->pending_dedents = 0;
        return;
    }

    size_t idx = 0;
    scanner->indent_depth = buffer[idx++];
    scanner->inside_string = buffer[idx++];
    scanner->string_delimiter = buffer[idx++];
    scanner->pending_dedents = buffer[idx++];

    for (uint8_t i = 0; i < scanner->indent_depth; i++) {
        scanner->indent_stack[i] =
            ((uint16_t)buffer[idx]) |
            ((uint16_t)buffer[idx + 1] << 8);
        idx += 2;
    }
}

// Count leading whitespace (spaces + tabs*4)
static uint16_t count_indent(TSLexer *lexer) {
    uint16_t indent = 0;
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
        if (lexer->lookahead == ' ') {
            indent++;
        } else {
            indent += 4;  // Tab = 4 spaces
        }
        lexer->advance(lexer, false);
    }
    return indent;
}

// Skip whitespace but not newlines
static void skip_whitespace(TSLexer *lexer) {
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
        lexer->advance(lexer, true);
    }
}

// Main scan function
bool tree_sitter_simple_external_scanner_scan(
    void *payload,
    TSLexer *lexer,
    const bool *valid_symbols
) {
    Scanner *scanner = payload;

    // Handle pending dedents
    if (scanner->pending_dedents > 0 && valid_symbols[DEDENT]) {
        scanner->pending_dedents--;
        scanner->indent_depth--;
        lexer->result_symbol = DEDENT;
        return true;
    }

    // Handle string tokens
    if (scanner->inside_string) {
        if (valid_symbols[STRING_END] &&
            lexer->lookahead == scanner->string_delimiter) {
            lexer->advance(lexer, false);
            scanner->inside_string = false;
            lexer->result_symbol = STRING_END;
            return true;
        }

        if (valid_symbols[STRING_CONTENT]) {
            bool has_content = false;
            while (lexer->lookahead != 0 &&
                   lexer->lookahead != scanner->string_delimiter &&
                   lexer->lookahead != '{' &&
                   lexer->lookahead != '\\') {
                lexer->advance(lexer, false);
                has_content = true;
            }
            if (has_content) {
                lexer->result_symbol = STRING_CONTENT;
                return true;
            }
        }
        return false;
    }

    // Handle string start
    if (valid_symbols[STRING_START] &&
        (lexer->lookahead == '"' || lexer->lookahead == '\'')) {
        scanner->string_delimiter = lexer->lookahead;
        scanner->inside_string = true;
        lexer->advance(lexer, false);
        lexer->result_symbol = STRING_START;
        return true;
    }

    // Handle newline and indentation
    if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
        // Skip the newline
        if (lexer->lookahead == '\r') {
            lexer->advance(lexer, true);
        }
        if (lexer->lookahead == '\n') {
            lexer->advance(lexer, true);
        }

        // Skip blank lines and comments
        while (true) {
            uint16_t indent = count_indent(lexer);

            // Skip blank lines
            if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
                if (lexer->lookahead == '\r') lexer->advance(lexer, true);
                if (lexer->lookahead == '\n') lexer->advance(lexer, true);
                continue;
            }

            // Skip comment lines
            if (lexer->lookahead == '#') {
                while (lexer->lookahead != '\n' &&
                       lexer->lookahead != '\r' &&
                       lexer->lookahead != 0) {
                    lexer->advance(lexer, true);
                }
                if (lexer->lookahead == '\r') lexer->advance(lexer, true);
                if (lexer->lookahead == '\n') lexer->advance(lexer, true);
                continue;
            }

            // Handle indentation change
            uint16_t current_indent = scanner->indent_stack[scanner->indent_depth - 1];

            if (indent > current_indent) {
                // INDENT
                if (valid_symbols[INDENT]) {
                    scanner->indent_stack[scanner->indent_depth++] = indent;
                    lexer->result_symbol = INDENT;
                    return true;
                }
            } else if (indent < current_indent) {
                // DEDENT(s)
                while (scanner->indent_depth > 1 &&
                       scanner->indent_stack[scanner->indent_depth - 1] > indent) {
                    scanner->pending_dedents++;
                    scanner->indent_depth--;
                }

                if (scanner->pending_dedents > 0 && valid_symbols[DEDENT]) {
                    scanner->pending_dedents--;
                    lexer->result_symbol = DEDENT;
                    return true;
                }
            }

            // NEWLINE (same indentation level)
            if (valid_symbols[NEWLINE]) {
                lexer->result_symbol = NEWLINE;
                return true;
            }

            break;
        }
    }

    // Handle NEWLINE at end of file
    if (lexer->eof(lexer)) {
        if (valid_symbols[DEDENT] && scanner->indent_depth > 1) {
            scanner->indent_depth--;
            lexer->result_symbol = DEDENT;
            return true;
        }
        if (valid_symbols[NEWLINE]) {
            lexer->result_symbol = NEWLINE;
            return true;
        }
    }

    return false;
}
```

---

## Rust Bindings

### Cargo.toml

```toml
[package]
name = "tree-sitter-simple"
version = "0.1.0"
edition = "2021"
description = "Tree-sitter grammar for the Simple programming language"
license = "MIT"
repository = "https://github.com/simple-lang/tree-sitter-simple"
keywords = ["tree-sitter", "parser", "simple"]
categories = ["parsing", "development-tools"]

[lib]
path = "src/lib.rs"
crate-type = ["cdylib", "rlib"]

[dependencies]
tree-sitter = "0.22"

[build-dependencies]
cc = "1.0"
```

### build.rs

```rust
// build.rs - Build script for compiling Tree-sitter grammar

fn main() {
    let src_dir = std::path::Path::new("src");

    let mut c_config = cc::Build::new();
    c_config.include(src_dir);
    c_config
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs");

    let parser_path = src_dir.join("parser.c");
    c_config.file(&parser_path);

    let scanner_path = src_dir.join("scanner.c");
    if scanner_path.exists() {
        c_config.file(&scanner_path);
    }

    c_config.compile("tree-sitter-simple");
}
```

### src/lib.rs

```rust
//! Tree-sitter grammar for the Simple programming language
//!
//! This crate provides Rust bindings for parsing Simple source code
//! using the Tree-sitter parsing library.

use tree_sitter::Language;

extern "C" {
    fn tree_sitter_simple() -> Language;
}

/// Returns the Tree-sitter Language for Simple.
///
/// # Safety
///
/// This function calls into C code but is safe because the
/// tree-sitter-simple grammar is generated and compiled correctly.
pub fn language() -> Language {
    unsafe { tree_sitter_simple() }
}

/// The content of the [`node-types.json`] file for this grammar.
pub const NODE_TYPES: &str = include_str!("../src/node-types.json");

/// The syntax highlighting queries for Simple.
pub const HIGHLIGHTS_QUERY: &str = include_str!("../queries/highlights.scm");

/// The indentation queries for Simple.
pub const INDENTS_QUERY: &str = include_str!("../queries/indents.scm");

/// The injection queries for Simple.
pub const INJECTIONS_QUERY: &str = include_str!("../queries/injections.scm");

/// The local variable queries for Simple.
pub const LOCALS_QUERY: &str = include_str!("../queries/locals.scm");

#[cfg(test)]
mod tests {
    use super::*;
    use tree_sitter::Parser;

    #[test]
    fn test_can_load_grammar() {
        let mut parser = Parser::new();
        parser.set_language(language()).expect("Error loading Simple grammar");
    }

    #[test]
    fn test_parse_function() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
fn add(a: i64, b: i64) -> i64:
    return a + b
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_struct() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
struct Point:
    x: f64
    y: f64
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_actor() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
actor Counter:
    state:
        value: i64 = 0

    on Inc(by: i64) async:
        self.value = self.value + by
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_lambda() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
let square = \x: x * x
items.map \item: item.name
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_handle_pool() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
handle_pool Enemy:
    capacity: 1024

let h: +Enemy = new+ Enemy(hp: 100)
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_pattern_matching() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
match result:
    case Ok(value):
        print value
    case Err(msg):
        print "Error: {msg}"
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_list_comprehension() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
let squares = [x * x for x in 0..10]
let evens = [x for x in items if x % 2 == 0]
let pairs = [(x, y) for x in 0..3 for y in 0..3]
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_slicing() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
let first_three = items[:3]
let last_three = items[-3:]
let reversed = items[::-1]
let every_other = items[::2]
let middle = items[1:5:2]
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_try_expression() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
fn process() -> Result<Data, Error>:
    let file = open(path)?
    let content = file.read()?
    return Ok(parse(content)?)
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_if_let() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
if let Some(value) = optional:
    process(value)
else:
    handle_none()

while let Some(item) = iter.next():
    print item
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_decorators() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
@cached
@logged
fn expensive_operation(x: i64) -> i64:
    return compute(x)

@retry(attempts: 3)
fn network_call():
    return fetch()
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_attributes() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
#[inline]
fn hot_path(x: i64) -> i64:
    return x * 2

#[derive(Debug, Clone, Eq)]
struct Point:
    x: f64
    y: f64
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_with_statement() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
with open("file.txt") as f:
    let content = f.read()
    process(content)

with open("in.txt") as inp, open("out.txt") as out:
    out.write(transform(inp.read()))
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_move_lambda() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
let counter = move \:
    count = count + 1
    count

let processor = move \x: expensive_compute(x, config)
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_or_patterns() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
match command:
    case "quit" | "exit" | "q":
        shutdown()
    case 1 | 2 | 3:
        print "small"
    case _:
        default()
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_range_patterns() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
match score:
    case 90..100:
        "A"
    case 80..90:
        "B"
    case _:
        "F"
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_module_declaration() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
#[strong]
mod sys

pub mod http
mod internal
#[no_gc]
pub mod driver
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_use_statements() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
use crate.core.prelude.Option
use crate.time.Instant
use crate.net.http.{Client, Request}
use crate.net.http.*
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_common_use() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
common use crate.core.base.*
common use crate.net.Url
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_export_use() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
export use router.Router
export use router.{Client, Request}
export use router.*
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_auto_import() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        let source = r#"
auto import router.route
auto import router.route_get
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }

    #[test]
    fn test_parse_init_spl() {
        let mut parser = Parser::new();
        parser.set_language(language()).unwrap();

        // Complete __init__.spl example
        let source = r#"
#[profile("server")]
mod http

pub mod router

export use router.Router
export use router.route
export use router.route_get

auto import router.route
auto import router.route_get
"#;

        let tree = parser.parse(source, None).unwrap();
        assert!(!tree.root_node().has_error());
    }
}
```

---

Next: [Parser Integration and Queries](lexer_parser_integration.md)
