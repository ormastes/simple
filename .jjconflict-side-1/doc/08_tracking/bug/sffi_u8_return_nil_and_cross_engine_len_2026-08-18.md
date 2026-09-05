# SFFI `-> [u8]` siblings: interpreter binds `nil`, and `rt_bytes_alloc` length disagrees across engines

**Date:** 2026-08-18
**Area:** interpreter / SFFI return marshalling
**Status:** open
**Found while:** verifying the premise of todo_db rows 6/40/96/155/355/418/487
(all seven are duplicate scanner hits of one TODO in
`src/lib/nogc_sync_mut/io/signature_sffi.spl`).

## Context

The original row claimed an SFFI wrapper declared `-> [u8]` bound
`Option::Some([bytes])`, breaking `.len()`. **That premise is stale** — see the
correction note in this directory. While sweeping siblings of that defect class
two *different*, still-live defects turned up.

## Defect A — interpreter binds `nil` for a declared `-> [u8]` extern

```simple
extern fn rt_file_read_bytes(path: text) -> [u8]
val buf = rt_file_read_bytes("/nonexistent/missing.bin")
buf.len()
```

`bin/simple test` (tree-walk interpreter):

```
✗ rt_file_read_bytes on a missing path binds an empty array, not Option
  semantic: method `len` not found on type `nil` (receiver value: nil)
Results: 5 total, 4 passed, 1 failed
```

The declared return type is a plain `[u8]`; binding `nil` violates it. This is
the same *class* as the original row (declared `[u8]`, bound something else),
with a different wrong value.

## Defect B — `rt_bytes_alloc(n).len()` disagrees between engines

Same fixture on both engines:

| engine | `rt_bytes_alloc(24).len()` | `rt_file_read_bytes(missing).len()` |
|---|---|---|
| `bin/simple test` (interpreter) | 24 | `nil`, no `.len()` |
| `bin/simple run` (Cranelift JIT) | **0** | 0 |

Raw JIT output:

```
alloc len=0
read len=0
```

The interpreter transports the real allocation length; the JIT reports 0. A
caller sizing a buffer off `.len()` gets a different answer per engine.

## Pinned by

`test/01_unit/compiler/sffi_byte_array_return_class_spec.spl` covers the
*working* part of the class (4 green, with a positive control proving the
extern path really executes). The two cases above are deliberately **excluded**
from that spec so it does not normalise the broken behaviour; re-add them as
the fix lands.

## Not fixed here

Root cause is in the extern return marshalling, and the two engines disagree,
so a one-engine patch would paper over Defect B. Left open rather than
half-fixed.
