# SDN Security Guide

This document describes security features in the SDN parser and best practices for handling untrusted input.

---

## Threat Model

SDN is designed to be safe by default:
- **No code execution** (unlike YAML's `!!python/object`)
- **No external references** (unlike XML's external entities)
- **No object construction** (unlike SnakeYAML deserialization)

However, SDN still has attack surfaces:
1. **Depth DoS** - Deeply nested structures can cause stack overflow
2. **Memory DoS** - Large strings or excessive cells can exhaust memory
3. **Prototype pollution** - Keys like `__proto__` can corrupt object prototypes
4. **Path traversal** - Keys like `../../etc/passwd` can access files
5. **Structural injection** - Unexpected tables/arrays in config files

---

## Security Levels

### Level 1: Trusted Input (Default)

Use for:
- Internal configuration files
- Data you control
- Pre-validated input

```rust
use simple_sdn::parse;

let value = parse("name: Alice\nage: 30")?;
```

**Risk:** None (trusted source)

---

### Level 2: Untrusted Input (Validation)

Use for:
- User-uploaded files
- Network data
- External APIs

```rust
use simple_sdn::parse_untrusted;

let value = parse_untrusted(user_input)?;
```

**Protection:**
- Rejects nesting depth > 50 (prevents stack overflow)
- Rejects strings > 1 MB (prevents memory exhaustion)
- Rejects > 1M cells (prevents DoS)

**Performance:** Two-pass (validate + parse), ~2x slower than default

---

### Level 3: Configuration Files (Flat Dict Only)

Use for:
- Application config files
- Environment variables
- Simple key-value stores

```rust
use simple_sdn::parse_config;

let config = parse_config(config_file)?;
```

**Protection:**
- Only allows flat key-value pairs
- Rejects nested dicts, arrays, tables
- Prevents structural injection

**Use case:** Prevent attackers from injecting complex structures into config files

---

### Level 4: Safe Keys (Injection Prevention)

Use for:
- Data that flows to JavaScript
- Database field names
- File paths

```rust
use simple_sdn::parse_safe;

let value = parse_safe(input)?;
```

**Protection:**
- Rejects `__proto__`, `constructor`, `prototype` (prototype pollution)
- Rejects `..`, `/`, `\` (path traversal)
- Rejects control characters in keys

**Use case:** Prevent injection when SDN keys become identifiers in other systems

---

## Custom Policies

Combine handlers for custom security policies:

```rust
use simple_sdn::{parser::Parser, NoopHandler, RestrictedHandler, SafeKeyHandler};

// Example 1: No tables, max depth 10
let handler = RestrictedHandler::new()
    .without_tables();
let noop = NoopHandler::with_limits(10, 1024, 1000);

let mut parser = Parser::new(input);
parser.parse_with_handler(noop)?; // Validate first
let mut parser = Parser::new(input);
let value = parser.parse_with_handler(handler)?; // Then parse

// Example 2: Flat config with safe keys
let config = parse_config(input)?; // Flat dict only
let safe = parse_safe(&config.to_sdn())?; // Validate keys
```

---

## Attack Examples

### 1. Depth DoS (Stack Overflow)

**Attack:**
```sdn
a:
  b:
    c:
      d:
        ... (1000 levels deep)
```

**Mitigation:**
```rust
let value = parse_untrusted(input)?; // Rejects depth > 50
```

---

### 2. Memory DoS (Large Strings)

**Attack:**
```sdn
payload: "x" * 1_000_000_000  # 1 GB string
```

**Mitigation:**
```rust
let value = parse_untrusted(input)?; // Rejects strings > 1 MB
```

---

### 3. Cell Count DoS

**Attack:**
```sdn
data: [1, 2, 3, ... 10_000_000 items]
```

**Mitigation:**
```rust
let value = parse_untrusted(input)?; // Rejects > 1M cells
```

---

### 4. Prototype Pollution

**Attack:**
```sdn
__proto__:
  isAdmin: true
```

**Impact:** If SDN is converted to JavaScript object, pollutes `Object.prototype`

**Mitigation:**
```rust
let value = parse_safe(input)?; // Rejects __proto__
```

---

### 5. Path Traversal

**Attack:**
```sdn
../../etc/passwd: read
```

**Impact:** If SDN keys are used as file paths, accesses sensitive files

**Mitigation:**
```rust
let value = parse_safe(input)?; // Rejects ../
```

---

### 6. Structural Injection (Config Files)

**Attack:**
```sdn
# Attacker adds to config.sdn:
admin_users |id, name|
  1, attacker
```

**Impact:** If config is flat dict, this injects a table structure

**Mitigation:**
```rust
let config = parse_config(input)?; // Rejects tables
```

---

## Security Limits

Default limits for `parse_untrusted()`:

| Limit | Default | Rationale |
|-------|---------|-----------|
| `max_depth` | 50 | Prevents stack overflow (typical stack: 8 MB) |
| `max_string_len` | 1 MB | Prevents memory exhaustion |
| `max_cell_count` | 1 million | Prevents DoS (1M cells ≈ 10 MB) |

Custom limits:

```rust
use simple_sdn::{parser::Parser, NoopHandler};

let noop = NoopHandler::with_limits(
    10,        // max_depth: strict for untrusted input
    100_000,   // max_string_len: 100 KB
    10_000,    // max_cell_count: 10K cells
);

let mut parser = Parser::new(input);
parser.parse_with_handler(noop)?;
```

---

## CVE References

SDN's security features prevent attacks similar to:

| CVE | System | Attack | SDN Mitigation |
|-----|--------|--------|----------------|
| CVE-2022-1471 | SnakeYAML | RCE via deserialization | No object construction |
| CVE-2025-61260 | OpenAI Codex | Command injection from config | `parse_config()` rejects nesting |
| CVE-2021-3918 | json-pointer | Prototype pollution | `parse_safe()` rejects `__proto__` |
| Billion Laughs | XML | Exponential expansion DoS | `max_depth` limit |

See `doc/research/data_format_parser_security_2026-01-31.md` for detailed analysis.

---

## Performance Impact

| Mode | Speed | Allocation | Use Case |
|------|-------|------------|----------|
| `parse()` | 100% (baseline) | Full tree | Trusted input |
| `parse_untrusted()` | ~50% (2-pass) | Full tree | Untrusted input |
| `parse_config()` | ~95% | Full tree | Config files |
| `parse_safe()` | ~98% | Full tree | Key validation |
| `NoopHandler` | ~1000% (10x faster) | Zero | Validation only |

**Note:** Performance figures are estimates. Actual performance depends on input size and structure.

---

## Best Practices

### 1. Choose the Right Security Level

```rust
// Internal config file → parse()
let config = parse(include_str!("config.sdn"))?;

// User upload → parse_untrusted()
let data = parse_untrusted(&user_file)?;

// App config → parse_config()
let settings = parse_config(&app_config)?;

// Database fields → parse_safe()
let schema = parse_safe(&schema_def)?;
```

### 2. Validate Early

```rust
// Validate before processing
match parse_untrusted(input) {
    Ok(value) => process(value),
    Err(e) if e.is_security_error() => {
        log::warn!("Security violation: {}", e);
        return Err("Invalid input");
    }
    Err(e) => return Err(e),
}
```

### 3. Defense in Depth

```rust
// Layer multiple handlers
parse_untrusted(input)?;  // Step 1: depth/size check
let config = parse_config(input)?;  // Step 2: structure check
let safe = parse_safe(&config.to_sdn())?;  // Step 3: key check
```

### 4. Log Security Errors

```rust
use simple_sdn::SdnError;

match parse_untrusted(input) {
    Err(SdnError::SecurityError { message, span }) => {
        log::error!(
            "Security violation at {:?}: {}",
            span,
            message
        );
        metrics::increment_counter!("sdn.security_rejection");
    }
    Err(e) => log::warn!("Parse error: {}", e),
    Ok(value) => process(value),
}
```

### 5. Rate Limit Untrusted Input

```rust
// Prevent DoS via repeated parse attempts
if parse_attempts > MAX_ATTEMPTS {
    return Err("Too many parse attempts");
}

let value = parse_untrusted(input)?;
```

---

## Security Checklist

Before deploying:

- [ ] All untrusted input uses `parse_untrusted()` or stricter
- [ ] Config files use `parse_config()` to prevent injection
- [ ] Keys flowing to other systems use `parse_safe()`
- [ ] Security errors are logged and monitored
- [ ] Appropriate rate limits are in place
- [ ] Custom limits are tuned for your use case
- [ ] Tests cover malicious input scenarios

---

## Reporting Security Issues

If you discover a security vulnerability in SDN:

1. **Do not** open a public GitHub issue
2. Email: security@simple-lang.org (TODO: set up)
3. Include:
   - Description of the vulnerability
   - Proof-of-concept code
   - Impact assessment
   - Suggested fix (if any)

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.2.0 | 2026-01-31 | Added handler architecture, security modes |
| 0.1.0 | 2026-01-01 | Initial release |

---

## Further Reading

- **Design Document:** `doc/design/sdn_handler_trait_design.md`
- **Security Research:** `doc/research/data_format_parser_security_2026-01-31.md`
- **Implementation Plan:** `doc/plan/sdn_handler_impl_plan.md`
- **OWASP:** [XXE Prevention](https://owasp.org/www-community/vulnerabilities/XML_External_Entity_%28XXE%29_Processing)
- **PyYAML:** [safe_load() documentation](https://pyyaml.org/wiki/PyYAMLDocumentation)
