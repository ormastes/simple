# Pipeline Native Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/pipeline_native_spec.spl`_

---

## Overview

Tests the full Pure Simple compilation pipeline:
Source → Parse → HIR → MIR → ISel → RegAlloc → Encode → ELF → Link → Run

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 2 |

## Test Structure

### Pipeline Native

- ✅ compiles fn main() -> exit 0
- ✅ produces non-empty ELF bytes

