# Native Compile ELF Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/native_compile_elf_spec.spl`_

---

## Overview

Tests generating a native binary from hand-crafted x86_64 instructions
through the ELF writer pipeline: instructions → ELF → link → run.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 2 |

## Test Structure

### Native Compile ELF

- ✅ generates a valid ELF binary from x86_64 machine code
- ✅ produces a linkable and runnable binary with exit 0

