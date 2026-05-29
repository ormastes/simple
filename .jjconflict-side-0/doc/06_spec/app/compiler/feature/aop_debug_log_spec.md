# AOP Debug Logger

**Feature ID:** #AOP-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/aop_debug_log_spec.spl`_

---

## Overview

Validates the AOP debug logging subsystem including enable/disable toggling,
entry creation with depth tracking, group pairing of enter/exit calls,
wildcard and prefix-based filter patterns, incremental entry querying,
and ring buffer trimming when the entry limit is exceeded.

## Syntax

```simple
debug_log_enable("parse_*")
val gid = debug_log_enter("my_func", "app.mcp.main", "Server", 42, "path=\"/src\"")
debug_log_exit("my_func", "app.mcp.main", gid, 0)
val entries = debug_log_get_entries()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### AOP Debug Logger

#### enable and disable

- ✅ starts disabled by default when SIMPLE_AOP_DEBUG not set
- ✅ enables with wildcard pattern
- ✅ enables with specific pattern
- ✅ disables logging
#### entry creation

- ✅ creates enter entry with correct fields
- ✅ creates exit entry paired with enter
- ✅ skips entries when disabled
#### depth tracking

- ✅ tracks nested call depth
#### group pairing

- ✅ assigns unique group IDs
- ✅ tracks parent group IDs
#### filter pattern

- ✅ filters by prefix pattern
- ✅ filters by module path
- ✅ matches exact function name
#### query entries

- ✅ returns entries since a given ID
#### ring buffer

- ✅ trims entries when exceeding max
#### clear

- ✅ resets all state

