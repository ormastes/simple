# MIR Complex Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/mir_complex_spec.spl`_

---

## Overview

Tests arithmetic, control flow (if/else), and multiple function calls
through the ISel → RegAlloc → Encode → ELF pipeline using manually
constructed MIR.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### MIR Complex

- ✅ compiles arithmetic and if/else MIR and outputs '42'

