# GOT/PLT Builder for Native Backend

**Feature ID:** #COMPILER-002 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/compiler/backend/native/got_plt_spec.spl`_

---

## Overview

Tests the Global Offset Table (GOT) and Procedure Linkage Table (PLT) builder for the native
x86_64 backend. Validates basic structure creation, GOT/PLT size calculations (8 bytes per GOT
entry, 16 bytes per PLT entry), x86_64 PLT stub generation including JMP opcode encoding and
RIP-relative addressing, symbol management with deduplication, sequential index assignment,
correct GOT offset allocation, and little-endian i32 encoding for the helper functions.

## Syntax

```simple
var builder = GotPltBuilder(got_entries: [], plt_entries: [], got_size: 0, plt_size: 0, next_got_offset: 0, next_plt_index: 0)
val index = builder.add_symbol("printf")
expect(builder.got_entries.len()).to_equal(1)

val stub = generate_plt_stub_x86_64(0, 0)
expect(stub.len()).to_equal(16)
expect(stub[0]).to_equal(0xFF)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### GOT/PLT Builder - Basic Structure

- ✅ creates new builder with empty state
- ✅ calculates GOT size correctly
- ✅ calculates PLT size correctly
### GOT/PLT Builder - PLT Stub Generation

- ✅ generates valid x86_64 PLT stub
- ✅ includes PLT index in stub
- ✅ includes GOT offset in stub
### GOT/PLT Builder - Symbol Management

- ✅ adds first symbol correctly
- ✅ allocates GOT entry with correct offset
- ✅ increments GOT offset by 8 bytes per symbol
- ✅ reuses existing symbol without duplication
### GOT/PLT Builder - Multiple Symbols

- ✅ handles multiple unique symbols
- ✅ assigns sequential indices to symbols
- ✅ assigns correct GOT offsets
### GOT/PLT Builder - Helper Functions

- ✅ encodes i32 in little-endian
- ✅ encodes zero correctly
- ✅ encodes small positive number

