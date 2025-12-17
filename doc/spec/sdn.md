# SDN - Simple Data Notation

**Version:** 1.0
**Status:** Specification
**Last Updated:** 2025-12-17

SDN is a minimal, token-efficient data notation format for configuration files and embedded data. Inspired by TOON but simpler, SDN combines YAML-style indentation with clean table syntax.

---

## Overview

### Design Goals

1. **Minimal syntax** - No unnecessary punctuation
2. **One-pass parsing** - LL(2) max lookahead
3. **Token efficient** - Optimized for LLM context windows
4. **Human readable** - Clear visual structure
5. **Embeddable** - Works as standalone files or embedded in Simple code

### Comparison with Other Formats

| Feature | JSON | YAML | TOML | TOON | SDN |
|---------|------|------|------|------|-----|
| Quote-free strings | ❌ | ✅ | Partial | ✅ | ✅ |
| Indentation blocks | ❌ | ✅ | ❌ | ✅ | ✅ |
| Inline & block forms | ❌ | ✅ | ✅ | Partial | ✅ |
| Table syntax | ❌ | ❌ | ✅ | ✅ | ✅ |
| Length declarations | ❌ | ❌ | ❌ | Required | ❌ |
| One-pass parse | ✅ | ❌ | ✅ | ✅ | ✅ |
| Typed tables | ❌ | ❌ | ❌ | ❌ | ✅ |

---

## Syntax

### Assignment Rules

| Operator | Usage | Form |
|----------|-------|------|
| `:` | Simple value or block start | Long form |
| `=` | Inline dict/array | Short form |
| `\|...\|` | Named table fields | Table form |

### Values

#### Primitives

```sdn
# Simple values (colon)
name: Alice
age: 30
active: true
ratio: 3.14

# Quote-free strings (identifier-like)
city: Boulder
status: pending

# Quoted strings (spaces/special chars)
message: "Hello, World!"
path: "/home/user/data"
```

#### Supported Types

| Type | Examples |
|------|----------|
| String (bare) | `Alice`, `localhost`, `pending` |
| String (quoted) | `"Hello World"`, `"has, comma"` |
| Integer | `42`, `-17`, `1_000_000` |
| Float | `3.14`, `-0.5`, `1.5e-10` |
| Boolean | `true`, `false` |
| Null | `null`, `nil` |

### Dict (Object)

#### Short Form (inline with `=`)

```sdn
point = {x: 10, y: 20}
config = {host: localhost, port: 8080, debug: true}
nested = {outer: {inner: value}}
```

#### Long Form (block with `:`)

```sdn
server:
    host: localhost
    port: 8080
    debug: true

# Nested blocks
database:
    primary:
        host: db1.example.com
        port: 5432
    replica:
        host: db2.example.com
        port: 5432
```

### Array (List)

#### Short Form (inline with `=`)

```sdn
names = [Alice, Bob, Carol]
numbers = [1, 2, 3, 4, 5]
mixed = [Alice, 30, true]
```

#### Long Form (block with `:`)

```sdn
features:
    auth
    logging
    metrics
    caching

# Array of objects
users:
    {name: Alice, role: admin}
    {name: Bob, role: user}
```

### Table

Tables represent arrays of uniform records - the most token-efficient way to express structured data.

#### Typed Table (Short Form)

```sdn
# Type declaration with inline values
coords: table{i32, i32} = [(10, 20), (30, 40), (50, 60)]

# Single row
point: table{f64, f64} = [(3.14, 2.71)]
```

#### Typed Table (Long Form)

```sdn
# Type declaration with block values
matrix: table{i32, i32, i32}
    1, 0, 0
    0, 1, 0
    0, 0, 1

coords: table{f64, f64}
    1.0, 2.0
    3.0, 4.0
    5.0, 6.0
```

#### Named Table (Long Form)

```sdn
# Field names with |...|
users |id, name, email, active|
    1, Alice, alice@example.com, true
    2, Bob, bob@example.com, true
    3, Carol, carol@example.com, false

# Complex values in tables
products |sku, name, price, tags|
    A001, "Widget Pro", 29.99, [electronics, gadgets]
    A002, "Gizmo Plus", 49.99, [electronics]
    B001, "Basic Tool", 9.99, [tools, hardware]
```

#### Named Table (Short Form)

```sdn
# Single row inline
point |x, y| 10, 20
person |name, age| Alice, 30
```

---

## Short Form vs Long Form Summary

| Construct | Short Form (`=`) | Long Form (`:`) |
|-----------|------------------|-----------------|
| Dict | `p = {x: 1, y: 2}` | `p:`<br>`    x: 1`<br>`    y: 2` |
| Array | `a = [1, 2, 3]` | `a:`<br>`    1`<br>`    2`<br>`    3` |
| Table (typed) | `p: table{i32, i32} = [(1,2), (3,4)]` | `p: table{i32, i32}`<br>`    1, 2`<br>`    3, 4` |
| Table (named) | `p \|x, y\| 1, 2` | `p \|x, y\|`<br>`    1, 2`<br>`    3, 4` |

---

## Complete Examples

### Configuration File

```sdn
# Application configuration
app:
    name: MyService
    version: 2.1.0
    environment: production

server:
    host: 0.0.0.0
    port: 8080
    workers: 4

database:
    driver: postgres
    host: localhost
    port: 5432
    name: myapp_prod
    pool_size: 10

cache:
    enabled: true
    backend: redis
    ttl: 3600

features = [auth, logging, metrics, rate_limiting]

rate_limits |endpoint, requests, window|
    /api/login, 5, 60
    /api/search, 100, 60
    /api/upload, 10, 300
```

### Data File

```sdn
# Employee directory
company: Acme Corp
department: Engineering

employees |id, name, title, salary, remote|
    1001, Alice Chen, "Senior Engineer", 150000, true
    1002, Bob Smith, "Staff Engineer", 180000, false
    1003, Carol Jones, "Engineering Manager", 200000, true
    1004, David Lee, "Junior Engineer", 90000, true

teams:
    backend:
        lead: 1003
        members = [1001, 1004]
    frontend:
        lead: 1002
        members = [1004]

office_locations |city, country, timezone|
    San Francisco, USA, America/Los_Angeles
    London, UK, Europe/London
    Tokyo, Japan, Asia/Tokyo
```

### Embedded in Simple Code

```simple
# SDN data embedded in Simple source
config:
    timeout: 30
    retries: 3

endpoints |name, url, method|
    users, /api/users, GET
    create, /api/users, POST
    delete, /api/users/{id}, DELETE

fn main():
    for endpoint in endpoints:
        print("{endpoint.name}: {endpoint.method} {endpoint.url}")
```

---

## Grammar (EBNF)

```ebnf
(* === TOP LEVEL === *)
document     = statement* ;

statement    = ident ':' value NEWLINE                          (* simple value *)
             | ident '=' inline_value NEWLINE                   (* short dict/array *)
             | ident ':' NEWLINE INDENT block DEDENT            (* long dict/array *)
             | ident ':' table_type '=' '[' tuple_list ']' NEWLINE    (* short typed table *)
             | ident ':' table_type NEWLINE INDENT rows DEDENT  (* long typed table *)
             | ident '|' field_list '|' row                     (* short named table *)
             | ident '|' field_list '|' NEWLINE INDENT rows DEDENT    (* long named table *)
             | COMMENT NEWLINE
             | NEWLINE
             ;

(* === VALUES === *)
value        = bare_string
             | quoted_string
             | number
             | bool
             | null
             | inline_value
             ;

inline_value = '{' pair_list? '}'                               (* dict *)
             | '[' value_list? ']'                              (* array *)
             ;

pair_list    = pair (',' pair)* ','? ;
pair         = ident ':' value ;

value_list   = value (',' value)* ','? ;

(* === BLOCKS === *)
block        = dict_block
             | array_block
             ;

dict_block   = (ident ':' value NEWLINE)+ ;

array_block  = (value NEWLINE)+ ;

(* === TABLES === *)
table_type   = 'table' '{' type_list '}' ;
type_list    = type_name (',' type_name)* ;
type_name    = ident ;

field_list   = ident (',' ident)* ;

tuple_list   = tuple (',' tuple)* ;
tuple        = '(' value_list ')' ;

rows         = row+ ;
row          = value (',' value)* NEWLINE ;

(* === TOKENS === *)
ident        = [A-Za-z_][A-Za-z0-9_]* ;
bare_string  = [A-Za-z_][A-Za-z0-9_./:-]* ;      (* extended chars for paths/urls *)
quoted_string = '"' ([^"\\] | '\\' .)* '"' ;
number       = '-'? [0-9]+ ('.' [0-9]+)? ([eE] [+-]? [0-9]+)? ;
bool         = 'true' | 'false' ;
null         = 'null' | 'nil' ;
COMMENT      = '#' [^\n]* ;
NEWLINE      = '\n' | '\r\n' ;
INDENT       = <increase in indentation> ;
DEDENT       = <decrease in indentation> ;
```

---

## Parsing

### One-Pass LL(2) Parser

SDN is designed for efficient one-pass parsing with maximum 2-token lookahead.

#### Decision Tree

```
parse_statement():
    tok = peek()

    if tok == COMMENT or tok == NEWLINE:
        return skip()

    if tok == IDENT:
        name = consume()
        next = peek()

        switch next:
            case ':':
                consume()
                return parse_colon_stmt(name)
            case '=':
                consume()
                return parse_inline_assign(name)
            case '|':
                return parse_named_table(name)
            default:
                error("Expected ':', '=', or '|'")

parse_colon_stmt(name):
    tok = peek()

    switch tok:
        case 'table':
            return parse_typed_table(name)
        case NEWLINE:
            consume()
            expect(INDENT)
            return parse_block(name)
        default:
            return parse_simple_value(name)

parse_block(name):
    first = peek()
    second = peek(2)

    if second == ':':
        return parse_dict_block(name)
    else:
        return parse_array_block(name)
```

#### Lookahead Requirements

| Context | Lookahead | Decision |
|---------|-----------|----------|
| After `ident` | 1 | `:` → colon_stmt, `=` → inline, `\|` → table |
| After `ident:` | 1 | `table` → typed, `NEWLINE` → block, else → value |
| After `ident: table{...}` | 1 | `=` → short, `NEWLINE` → long |
| In block | 2 | `ident:` → dict, else → array |

---

## SDN Crate Structure

SDN is implemented as a standalone Rust crate with library and CLI.

### Crate Layout

```
src/sdn/
├── Cargo.toml              # Crate manifest
├── src/
│   ├── lib.rs              # Library entry point
│   ├── lexer.rs            # Tokenizer with INDENT/DEDENT
│   ├── parser.rs           # One-pass LL(2) parser
│   ├── ast.rs              # AST node definitions
│   ├── value.rs            # Runtime value types (SdnValue enum)
│   ├── error.rs            # Error types with span info
│   ├── serde.rs            # Optional serde integration
│   └── update.rs           # Basic embedded update operations
└── src/bin/
    └── sdn.rs              # CLI executable
```

### Library API

```rust
// src/sdn/src/lib.rs

pub use ast::*;
pub use value::SdnValue;
pub use error::SdnError;
pub use parser::parse;
pub use update::SdnDocument;

/// Parse SDN string into value tree
pub fn parse(input: &str) -> Result<SdnValue, SdnError>;

/// Parse SDN file
pub fn parse_file(path: &Path) -> Result<SdnValue, SdnError>;

/// Parse and return editable document
pub fn parse_document(input: &str) -> Result<SdnDocument, SdnError>;
```

### Value Types

```rust
// src/sdn/src/value.rs

#[derive(Debug, Clone, PartialEq)]
pub enum SdnValue {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Array(Vec<SdnValue>),
    Dict(IndexMap<String, SdnValue>),
    Table {
        fields: Option<Vec<String>>,    // Named fields or None for typed
        types: Option<Vec<String>>,     // Type names or None for named
        rows: Vec<Vec<SdnValue>>,
    },
}

impl SdnValue {
    pub fn get(&self, key: &str) -> Option<&SdnValue>;
    pub fn get_mut(&mut self, key: &str) -> Option<&mut SdnValue>;
    pub fn as_str(&self) -> Option<&str>;
    pub fn as_i64(&self) -> Option<i64>;
    pub fn as_bool(&self) -> Option<bool>;
    pub fn as_array(&self) -> Option<&[SdnValue]>;
    pub fn as_dict(&self) -> Option<&IndexMap<String, SdnValue>>;
}
```

### Document Update API

```rust
// src/sdn/src/update.rs

/// Editable SDN document preserving formatting
pub struct SdnDocument {
    source: String,
    root: SdnValue,
    spans: HashMap<String, Span>,  // Path -> source span
}

impl SdnDocument {
    /// Get value at path (e.g., "server.port")
    pub fn get(&self, path: &str) -> Option<&SdnValue>;

    /// Set value at path, preserving surrounding formatting
    pub fn set(&mut self, path: &str, value: SdnValue) -> Result<(), SdnError>;

    /// Delete value at path
    pub fn delete(&mut self, path: &str) -> Result<(), SdnError>;

    /// Insert into array at path
    pub fn push(&mut self, path: &str, value: SdnValue) -> Result<(), SdnError>;

    /// Render document back to string
    pub fn to_string(&self) -> String;

    /// Write to file
    pub fn write_file(&self, path: &Path) -> Result<(), SdnError>;
}
```

### CLI Usage

```bash
# Parse and validate
sdn check config.sdn

# Parse and output as JSON
sdn to-json config.sdn

# Parse JSON and output as SDN
sdn from-json config.json

# Query value at path
sdn get config.sdn server.port

# Set value at path
sdn set config.sdn server.port 9090

# Pretty print
sdn fmt config.sdn
```

---

## Embedding in Simple

SDN can be embedded in Simple source files for inline configuration.

### Data Block Syntax

```simple
# Inline SDN block
data config:
    server:
        host: localhost
        port: 8080
    features = [auth, logging]

# Access like normal struct
print(config.server.host)
```

### File Loading

```simple
# Load external SDN file
config = sdn::load("config.sdn")

# Update and save
config.set("server.port", 9090)
config.save()
```

---

## TOON vs SDN Comparison

```
┌────────────┬─────────────────────────┬───────────────────────────────────┐
│ Construct  │ TOON                    │ SDN                               │
├────────────┼─────────────────────────┼───────────────────────────────────┤
│ Value      │ name: Alice             │ name: Alice                       │
├────────────┼─────────────────────────┼───────────────────────────────────┤
│ Dict short │ (none)                  │ p = {x: 1, y: 2}                  │
│ Dict long  │ p:                      │ p:                                │
│            │   x: 1                  │     x: 1                          │
├────────────┼─────────────────────────┼───────────────────────────────────┤
│ Array short│ items[3]: a,b,c         │ items = [a, b, c]                 │
│ Array long │ items[3]:               │ items:                            │
│            │  a                      │     a                             │
│            │  b                      │     b                             │
├────────────┼─────────────────────────┼───────────────────────────────────┤
│ Table short│ (none)                  │ p: table{i32,i32} = [(1,2),(3,4)] │
│ Table long │ hikes[3]{id,name,km}:   │ hikes |id, name, km|              │
│            │  1,Blue Lake,7.5        │     1, Blue Lake, 7.5             │
│            │  2,Ridge,9.2            │     2, Ridge, 9.2                 │
└────────────┴─────────────────────────┴───────────────────────────────────┘
```

### Key Differences

| Aspect | TOON | SDN |
|--------|------|-----|
| Array length | Required `[N]` | Inferred |
| Table header | `{fields}:` | `\|fields\|` |
| Inline dict | Not supported | `= {...}` |
| Inline array | `a,b,c` (no brackets) | `= [a, b, c]` |
| Typed tables | Not supported | `table{types}` |
| Short/long forms | Implicit | Explicit (`=` vs `:`) |

---

## Related Specifications

- [Syntax](syntax.md) - Simple language syntax
- [Types](types.md) - Type system
- [Data Structures](data_structures.md) - Structs, classes, enums

---

## Implementation Status

| Component | Status | Notes |
|-----------|--------|-------|
| Specification | ✅ | This document |
| Lexer | 📋 | Planned |
| Parser | 📋 | Planned |
| Value types | 📋 | Planned |
| Document update | 📋 | Planned |
| CLI | 📋 | Planned |
| Simple embedding | 📋 | Planned |
