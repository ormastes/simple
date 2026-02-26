# SDN - Simple Data Notation

A minimal, token-efficient data notation format for configuration files and embedded data.

## Features

- **Minimal syntax** with no unnecessary punctuation
- **One-pass LL(2) parsing** for fast compilation
- **Token efficient** for LLM context windows
- **Human readable** with clear visual structure
- **Security-first** with multiple validation modes
- **Zero dependencies** (except indexmap and thiserror)

## Quick Start

```rust
use simple_sdn::parse;

let src = r#"
name: Alice
age: 30
server:
    host: localhost
    port: 8080
"#;

let doc = parse(src)?;
assert_eq!(doc.get("name").and_then(|v| v.as_str()), Some("Alice"));
assert_eq!(doc.get_path("server.port").and_then(|v| v.as_i64()), Some(8080));
```

## Security

SDN provides multiple parsing modes for different trust levels:

### Trusted Input (Default)
```rust
use simple_sdn::parse;

let value = parse("name: Alice")?;
```

### Untrusted Input (Validation)
```rust
use simple_sdn::parse_untrusted;

// Rejects: deep nesting (>50), large strings (>1MB), excessive cells (>1M)
let value = parse_untrusted(user_input)?;
```

### Configuration Files (Flat Structure Only)
```rust
use simple_sdn::parse_config;

// Rejects: tables, arrays, nesting
let config = parse_config("debug: true\nport: 8080")?;
```

### Safe Keys (Injection Prevention)
```rust
use simple_sdn::parse_safe;

// Rejects: __proto__, constructor, ../, control chars
let value = parse_safe(input)?;
```

See [SECURITY.md](SECURITY.md) for detailed security documentation.

## Syntax Overview

### Values
```sdn
name: Alice           # bare string
message: "Hello"      # quoted string
age: 30               # integer
ratio: 3.15           # float
active: true          # boolean
empty: null           # null
```

### Dictionaries
```sdn
# Short form (inline)
point = {x: 10, y: 20}

# Long form (block)
server:
    host: localhost
    port: 8080
```

### Arrays
```sdn
# Short form (inline)
names = [Alice, Bob, Carol]

# Long form (block)
features:
    auth
    logging
    metrics
```

### Tables
```sdn
# Named table
users |id, name, email|
    1, Alice, alice@example.com
    2, Bob, bob@example.com

# Typed table
coords: table{i32, i32} = [(10, 20), (30, 40)]
```

## Advanced Usage

### Custom Validation

```rust
use simple_sdn::{parser::Parser, NoopHandler};

// Validate without allocating
let mut parser = Parser::new(input);
let noop = NoopHandler::with_limits(
    10,        // max_depth
    100_000,   // max_string_len
    10_000,    // max_cell_count
);
parser.parse_with_handler(noop)?;
```

### Custom Policies

```rust
use simple_sdn::{parser::Parser, RestrictedHandler};

// No tables allowed
let handler = RestrictedHandler::new().without_tables();
let mut parser = Parser::new(input);
let value = parser.parse_with_handler(handler)?;
```

### Editable Documents

```rust
use simple_sdn::SdnDocument;

let mut doc = SdnDocument::parse("port: 8080")?;
doc.set("port", simple_sdn::SdnValue::Int(9090))?;
let output = doc.to_sdn();
```

## Architecture

SDN uses a handler-based architecture that separates:
- **Data processing** (`DataHandler`) - primitives (int, string, bool, etc.)
- **Operation processing** (`OpHandler`) - containers (dict, array, table)

This enables:
- Zero-allocation validation
- Security policies
- Custom processing pipelines

See [doc/design/sdn_handler_trait_design.md](../../doc/design/sdn_handler_trait_design.md) for details.

## Performance

| Mode | Speed | Allocation | Use Case |
|------|-------|------------|----------|
| `parse()` | Baseline (100%) | Full tree | Trusted input |
| `parse_untrusted()` | ~50% (2-pass) | Full tree | Untrusted input |
| `parse_config()` | ~95% | Full tree | Config files |
| `NoopHandler` | ~1000% (10x faster) | Zero | Validation only |

## Security Features

- **No code execution** (unlike YAML's `!!python/object`)
- **No external references** (unlike XML's external entities)
- **No object construction** (unlike SnakeYAML)
- **Depth limits** (prevents stack overflow)
- **Size limits** (prevents memory exhaustion)
- **Key validation** (prevents prototype pollution & path traversal)

Mitigates attacks similar to:
- CVE-2022-1471 (SnakeYAML RCE)
- CVE-2025-61260 (OpenAI Codex command injection)
- CVE-2021-3918 (Prototype pollution)

## Testing

```bash
cargo test -p simple-sdn
```

**Test Coverage:**
- 65 parser tests
- 18 handler unit tests
- 25 integration tests
- 11 doc-tests
- **Total:** 119 tests, 0 failures

## Documentation

- **Security Guide:** [SECURITY.md](SECURITY.md)
- **Design Document:** [doc/design/sdn_handler_trait_design.md](../../doc/design/sdn_handler_trait_design.md)
- **Implementation Plan:** [doc/plan/sdn_handler_impl_plan.md](../../doc/plan/sdn_handler_impl_plan.md)
- **Security Research:** [doc/research/data_format_parser_security_2026-01-31.md](../../doc/research/data_format_parser_security_2026-01-31.md)

## License

MIT OR Apache-2.0

## Contributing

See [CONTRIBUTING.md](../../CONTRIBUTING.md) (TODO)

## Changelog

See [CHANGELOG.md](CHANGELOG.md) (TODO)
