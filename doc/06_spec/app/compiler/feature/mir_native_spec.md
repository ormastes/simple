# MIR Native Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/mir_native_spec.spl`_

---

## Overview

Tests the MIR → Native Backend pipeline by constructing a MirModule manually
and running it through ISel → RegAlloc → Encode → ELF → Link → Run.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 3 |

## Test Structure

### MIR Native

- ✅ runs ISel on manually constructed MIR module
- ✅ produces non-empty ELF from MIR module
- ✅ runs hello MIR binary and produces correct output

