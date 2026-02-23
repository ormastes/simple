# TOML to SDN Migration Guide

## Overview

Simple Language has migrated from TOML to SDN (Simple Data Notation) for all configuration files. This guide explains the migration process and format differences.

## Why SDN?

- **Token efficiency**: 30-50% fewer tokens than TOML (important for LLM context)
- **Simpler syntax**: No unnecessary punctuation like `[sections]` or `=` for nested structures
- **Native format**: SDN is Simple's own format, better integration with tooling
- **Consistent**: All Simple data files now use the same format

## Format Comparison

### Package Manifest

**TOML (legacy):**
```toml
[package]
name = "my-project"
version = "1.0.0"
authors = ["Alice <alice@example.com>"]
license = "MIT"

[dependencies]
http = "2.0"

[dependencies.json]
version = "1.5"
features = ["serde"]

[features]
default = ["logging"]
logging = []
```

**SDN (preferred):**
```sdn
package:
  name: my-project
  version: 1.0.0
  authors: [Alice <alice@example.com>]
  license: MIT

dependencies:
  http: 2.0
  json:
    version: 1.5
    features: [serde]

features:
  default: [logging]
  logging: []
```

### Test Configuration

**TOML (legacy):**
```toml
[test]
parallel = false
timeout = 120

[test.cpu_throttle]
enabled = true
threshold = 70
```

**SDN (preferred):**
```sdn
test:
  parallel: false
  timeout: 120
  cpu_throttle:
    enabled: true
    threshold: 70
```

## Migration Steps

### For Existing Projects

1. **Check current format:**
   ```bash
   ls simple.{toml,sdn} simple.test.{toml,sdn}
   ```

2. **Create SDN versions:**
   - Copy your `simple.toml` content
   - Convert to SDN syntax (see examples above)
   - Save as `simple.sdn`

3. **Validation:**
   ```bash
   # Test that the new manifest works
   simple check
   simple test --list
   ```

4. **Remove old TOML files (optional):**
   ```bash
   # Only after verifying SDN files work
   rm simple.toml simple.test.toml
   ```

### For New Projects

New projects automatically use SDN:
```bash
simple init my-project
# Creates simple.sdn (not simple.toml)
```

## Backwards Compatibility

The Simple tooling supports **both formats** during the transition:

- `simple.sdn` is **preferred** (checked first)
- `simple.toml` still works (legacy support)
- Mix not recommended (one format per project)

**Resolution order:**
1. Check for `simple.sdn`
2. Fall back to `simple.toml` if `.sdn` not found
3. Error if neither exists

## Common Conversions

### Arrays

```toml
# TOML
features = ["auth", "logging"]
```
```sdn
# SDN
features: [auth, logging]
```

### Nested Objects

```toml
# TOML
[server.database]
host = "localhost"
port = 5432
```
```sdn
# SDN
server:
  database:
    host: localhost
    port: 5432
```

### Booleans and Numbers

```toml
# TOML (quotes optional)
enabled = true
timeout = 30
ratio = 1.5
```
```sdn
# SDN (no quotes needed)
enabled: true
timeout: 30
ratio: 1.5
```

### Strings

```toml
# TOML (quotes required)
name = "my-project"
description = "A Simple project"
```
```sdn
# SDN (quotes optional for simple strings)
name: my-project
description: "A Simple project"
```

## Automated Migration (Future)

We plan to add automated migration tools:

```bash
# Not yet implemented
simple migrate toml-to-sdn simple.toml
# Would generate simple.sdn
```

For now, manual conversion is required (see examples above).

## SDN Syntax Reference

Full SDN syntax: `doc/guide/sdn_syntax_guide.md`

Quick reference:

```sdn
# Comments start with #

# Key-value pairs
key: value
string: bare or "quoted"
number: 42
float: 3.14
bool: true
null: null

# Arrays (short form)
list: [item1, item2, item3]

# Arrays (long form)
list:
  item1
  item2
  item3

# Objects/Dicts
object:
  key1: value1
  nested:
    key2: value2

# Tables (for structured data)
users |id, name, role|
  1, Alice, admin
  2, Bob, user
```

## Migration Checklist

- [ ] Backup existing `simple.toml` and `simple.test.toml`
- [ ] Create `simple.sdn` from `simple.toml`
- [ ] Create `simple.test.sdn` from `simple.test.toml` (if exists)
- [ ] Test with `simple check` and `simple test --list`
- [ ] Update any scripts that reference `.toml` files
- [ ] Consider removing old `.toml` files after verification
- [ ] Update team documentation to use `.sdn` format

## Troubleshooting

**Error: "Missing package section"**
- Ensure `package:` section exists in `simple.sdn`
- Check indentation (2 spaces per level)

**Error: "Invalid manifest format"**
- Check SDN syntax (colons, not equals signs)
- Arrays use brackets: `[item1, item2]`
- No section headers like `[package]`

**Dependencies not found:**
- Verify dependency format in `dependencies:` section
- Path dependencies still use same format

## Support

- SDN format spec: `doc/format/sdn_specification.md`
- Parser implementation: `src/rust/sdn/`
- Questions: Open an issue on GitHub

## Timeline

- **v0.2.0** (current): Both TOML and SDN supported
- **v0.3.0**: SDN preferred, TOML deprecated warnings
- **v1.0.0**: TOML support removed, SDN only

Migrate early to avoid breaking changes in v1.0!
