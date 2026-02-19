# Config Loader Specification

**Feature ID:** TBD | **Category:** Configuration / File Loading | **Status:** Implemented

_Source: `test/feature/app/config_loader_spec.spl`_

---

## Overview

The config loader provides a Simple-native configuration format using `.spl`
syntax with variable assignments. It supports hierarchical config loading
with directory-based precedence.

## Config File Format

```simple
# Numbers
port = 8080
timeout = 30.5

# Booleans
logging = true
debug = false

# Strings
name = "MyApp"

# Identifiers (constants)
mode = PRODUCTION

# Arrays
ports = [8080, 8081, 8082]

# Nested values (dotted keys)
train.epochs = 100
train.lr = 0.001
```

## Hierarchy & Precedence

Config files are searched from the current directory up to the project root.
Configs closer to the current directory override those higher in the hierarchy.

```
/project/__init__.spl          (lowest precedence)
/project/subdir/__init__.spl   (highest precedence)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### Config File Parsing

- ✅ parses basic integers
- ✅ parses floats
- ✅ parses booleans
- ✅ parses strings
- ✅ parses identifiers as constants
- ✅ parses arrays
- ✅ parses nested values with dotted keys
- ✅ skips comments
- ✅ skips empty lines
- ✅ handles multiline config

