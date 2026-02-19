# Driver Native Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/driver_native_spec.spl`_

---

## Overview

Tests compiling a simple program through the full compiler driver pipeline
using the native backend (Parse → HIR → MIR → ISel → RegAlloc → Encode → ELF).

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Driver Native

- ✅ compiles a simple function via driver and exits 0

