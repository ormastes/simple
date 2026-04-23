# Target-Based Mutability Defaults

Simple supports target-based compilation modes that change the default mutability of collections. In the general (default) target, arrays and dicts are mutable, allowing `push` and key assignment without explicit `var` declarations. Under `--target=embedded`, collections default to immutable to reduce memory overhead and prevent accidental mutation in resource-constrained environments. This spec validates the general-mode mutable defaults for arrays and dicts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-009 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/target_defaults_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Simple supports target-based compilation modes that change the default mutability of
collections. In the general (default) target, arrays and dicts are mutable, allowing
`push` and key assignment without explicit `var` declarations. Under `--target=embedded`,
collections default to immutable to reduce memory overhead and prevent accidental mutation
in resource-constrained environments. This spec validates the general-mode mutable
defaults for arrays and dicts.

## Syntax

```simple
var arr = [1, 2, 3]
arr.push(4)
expect arr.len() == 4

val dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Target Mode | A compile-time flag (`--target=`) that sets platform-specific defaults |
| General Mode | Default target where arrays and dicts are mutable out of the box |
| Embedded Mode | Target where collections default to immutable for safety and efficiency |
| Mutability Default | Whether a collection allows modification without an explicit `var` binding |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/target_defaults/result.json` |

## Scenarios

- makes arrays mutable by default
- makes dicts mutable by default
