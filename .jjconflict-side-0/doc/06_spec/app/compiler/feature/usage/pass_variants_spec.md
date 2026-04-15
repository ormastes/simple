# Pass Keyword Variants

Tests the enhanced pass keyword with semantic distinctions: `pass_todo` for unimplemented code markers, `pass_do_nothing`/`pass_dn` for intentional no-ops, and `pass` for generic backward-compatible no-ops. All variants work as statements, function in control flow contexts, and accept optional descriptive message arguments.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-002 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/pass_variants_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the enhanced pass keyword with semantic distinctions: `pass_todo` for
unimplemented code markers, `pass_do_nothing`/`pass_dn` for intentional no-ops,
and `pass` for generic backward-compatible no-ops. All variants work as
statements, function in control flow contexts, and accept optional descriptive
message arguments.

## Syntax

```simple
pass_todo("implement error handling")
pass_do_nothing("intentional stub for interface")
pass_dn
pass
```
Pass Variants Specification

Tests the enhanced pass keyword with semantic distinctions:
- pass_todo: Marks unimplemented code (TODO marker)
- pass_do_nothing / pass_dn: Intentional no-op
- pass: Generic no-op (backward compatible)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/pass_variants/result.json` |

## Scenarios

- pass as statement
- pass with message
- pass_todo as statement
- pass_todo with message
- pass_do_nothing as statement
- pass_do_nothing with message
- pass_dn as statement
- pass_dn with message
- function with pass
- function with pass_todo
- function with pass_do_nothing
- function with pass_dn
- pass in if branch
- pass_todo in else branch
- pass_do_nothing in loop
- pass_dn in conditional
- pass with descriptive message
- pass_todo with reason
- pass_do_nothing with explanation
- pass_dn with context
