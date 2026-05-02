# Aop Debug Log Specification

AOP Debug Logger

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/aop_debug_log_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

AOP Debug Logger

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
AOP Debug Logger Specification

Self-contained implementation of AOP debug logging with depth tracking,
group pairing, and ring buffer. No compiler imports needed.
Uses array concat (items = items + [x]) instead of .push() because
.push() does not persist on module-level arrays in the runtime.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/aop_debug_log/result.json` |

## Scenarios

- starts disabled by default
- enables with wildcard pattern
- enables with specific pattern
- disables logging
- creates enter entry with correct fields
- creates exit entry paired with enter
- skips entries when disabled
- tracks nested call depth
- assigns unique group IDs
- tracks parent group IDs
- filters by prefix pattern
- filters by module path
- matches exact function name
- returns entries since a given ID
- trims entries when exceeding max
- resets all state
