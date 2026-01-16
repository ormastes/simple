# SMF Binary Format

*Source: `simple/std_lib/test/features/infrastructure/smf_spec.spl`*

---

# SMF Binary Format

**Feature ID:** #9
**Category:** Infrastructure
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

Simple Module Format - binary executable format for compiled Simple programs. Supports
sections, symbols, relocations, and memory mapping for efficient loading and execution.

## Syntax

Binary file structure with magic number "SMF\0", sections (Code, Data, RoData, BSS,
Reloc, SymTab, StrTab, Debug), and metadata for 64-bit architectures.

## Implementation

**Files:**
- src/loader/src/smf/mod.rs - Main SMF module
- src/loader/src/smf/header.rs - SMF header parsing
- src/loader/src/smf/section.rs - Section management
- src/loader/src/smf/symbol.rs - Symbol table handling
- src/loader/src/smf/reloc.rs - Relocation processing
- src/loader/src/loader.rs - Module loader
- src/loader/src/module.rs - Loaded module representation

**Tests:**
- src/driver/tests/runner_tests.rs

**Dependencies:** Feature #5
**Required By:** None

## Notes

Magic: SMF\0. Sections: Code, Data, RoData, BSS, Reloc, SymTab, StrTab, Debug.
Supports 64-bit architectures.
