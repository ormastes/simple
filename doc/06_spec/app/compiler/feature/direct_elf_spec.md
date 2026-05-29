# Direct ELF Writing (Phase 2.1)

**Feature ID:** #COMPILER-004 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/compiler/linker/direct_elf_spec.spl`_

---

## Overview

Tests the direct ELF binary writing functionality that bypasses the assembler intermediary.
Validates ELF magic number verification (0x7F 'E' 'L' 'F'), rejection of invalid magic bytes
for each of the four positions, rejection of too-small files, file operations including creation
with correct permissions, overwriting existing files, handling of empty paths, and integration
between write_elf_bytes_to_file and verify_elf_file for valid ELF, non-ELF, and non-existent files.

## Syntax

```simple
val elf_bytes: [u8] = [127, 69, 76, 70, 2, 1, 1, 0]
val result = write_elf_bytes_to_file(test_path, elf_bytes)
expect(result.is_ok()).to_equal(true)

val verify_result = verify_elf_file(test_path)
expect(verify_result).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Phase 2.1: Direct ELF Writing

#### Helper Functions

- ✅ detects direct ELF writing should be enabled by default
- ✅ verifies valid ELF file
- ✅ rejects invalid ELF magic number
- ✅ rejects too-small file
#### ELF Magic Number Verification

- ✅ accepts correct ELF magic: 0x7F 'E' 'L' 'F'
- ✅ rejects wrong first byte
- ✅ rejects wrong second byte
- ✅ rejects wrong third byte
- ✅ rejects wrong fourth byte
#### File Operations

- ✅ creates file with correct permissions
- ✅ overwrites existing file
- ✅ handles empty path gracefully
#### Integration with verify_elf_file

- ✅ verify returns false for non-existent file
- ✅ verify returns false for non-ELF file
- ✅ verify returns true for valid ELF

