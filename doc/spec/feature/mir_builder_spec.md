# MIR Builder Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/mir_builder_spec.spl`_

---

## Overview

Tests the MirBuilder API produces correct MIR that the native backend
can compile: builds a function using the builder API and runs it.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 2 |

## Test Structure

### MIR Builder

- ✅ builds a function module with MirBuilder API
- ✅ compiles MirBuilder module and outputs '30'

