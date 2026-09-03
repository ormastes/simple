# Interpolating a struct in native codegen silently renders `<invalid-heap:0x...>`

**Date:** 2026-09-02
**Status:** OPEN — no guard exists
**Severity:** HIGH — silently destroys diagnostics, and does so only on failure paths

## What happens

`"{some_struct}"` in native-compiled Simple does not render the struct's fields
and does not fail. It emits the literal text `<invalid-heap:0x{pointer:x}>`.

Mechanism, exactly:

- `src/compiler_rust/runtime/src/value/heap.rs:8` — `HeapObjectType` has
  **no `Struct` variant**: String 0x01, Array 0x02, Dict 0x03, Tuple 0x04,
  Object 0x05, Closure 0x06, Enum 0x07, Future 0x08, ... A native-codegen
  struct pointer therefore carries no header the runtime recognises.
- `src/compiler_rust/runtime/src/value/sffi/io_print.rs:474` —
  `heap_value_to_display_string` takes its
  `let Some(object_type) = v.heap_type() else { return format!("<invalid-heap:0x{:x}>", ...) }`
  arm and returns that string.

A CLASS instance renders as `<object@0x...>` (`io_print.rs:562`) — also useless
but distinguishable. The `invalid-heap` spelling is the fingerprint of a
**struct**.

## Why it matters

It cost a day of Windows-bootstrap investigation. The Stage 2 receiver gate
reported

```
Linking failed: Windows MSVC linking failed: <invalid-heap:0x1e9548829b1>
```

from `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:877`,
which interpolated `{e}` where `e` is a `LinkError` **struct**
(`70.backend/linker/link.spl:108`). The linker's real message
(`e.message`) was never read. Multiple prior investigations reasoned about a
message the code never asked for. See
`stage2_receiver_link_error_text_is_invalid_heap_2026-09-02.md`.

Second live instance found in the same sweep:
`_LinkerWrapper/shared_linking.spl:293` (`"Windows MSVC DLL linking failed: {e}"`).
Both are now `{e.message}`.

The failure mode is structurally nasty: `"{err_struct}"` appears overwhelmingly
on ERROR paths, so it only fires once something else has already gone wrong,
and it converts that failure into an undiagnosable one.

## Not established

- How many other `"{struct}"` sites exist in the tree. No census has been run.
  A census is the obvious next step and needs type information, so a grep alone
  will not do it.
- Whether the interpreter renders these correctly (it appears to), which would
  make this an interpreter/native divergence as well as a diagnostic loss.

## Fix options (not yet chosen)

1. **Compile-time**: make interpolating a struct with no display an error, or a
   lint. Cheapest to reason about; forces the author to name a field.
2. **Runtime**: give structs a heap header and a field-wise render, matching
   the interpreter. Larger, but removes an interpreter/native divergence.
3. Minimum viable: a lint rule flagging `{ident}` where `ident`'s type is a
   struct without a display, in the same family as `cow_alias_hotpath`.

There is currently **no guard of any kind** for this class.
