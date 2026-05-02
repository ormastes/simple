# Target-Based Mutability Defaults

**Feature ID:** #LANG-009 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/target_defaults_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 2 |

## Test Structure

### Target-Based Mutability Defaults

#### General Mode (Default)

- ✅ makes arrays mutable by default
- ✅ makes dicts mutable by default

