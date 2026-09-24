# Bug: Generic struct type parameter not resolved in impl block

## Closed 2026-09-13 — Fixed: a struct type parameter resolves inside its `impl` block

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the entry's minimal repro compiles and runs. `struct Digest<N>: payload: [u8]` with `impl Digest<N>: fn len() -> i64: self.payload.len()`, called as `Digest<i64>(payload: [1u8, 2u8]).len()`, prints `2`. No `Unknown type: N`, no `Unknown type: Id`.
- **inferred**: the sibling shapes the entry names (`PostingList<Id>`, `Embedding<D>`) are the same construct — a type parameter referenced from the `impl` — so they are covered by the same resolution; they were not separately exercised.
- Note: `<>` is the sanctioned generic syntax per CLAUDE.md, and that is what was tested.

**ID:** crypto_digest_generic_struct_2026-06-15
**Date:** 2026-06-15
**Status:** CLOSED 2026-09-13 (fixed). **Severity:** P2 (language limitation, workaround exists)
**Component:** Compiler / Type system — generics on struct definitions

## Summary

Attempting to define a const-generic struct `Digest<N>` (where N is a
phantom size parameter) causes a compile-time error "Unknown type: N" (or
"Unknown type: Id") when the type parameter is referenced inside the `impl`
block.  The same pattern was observed with `PostingList<Id>` and
`Embedding<D>`.

## Minimal Repro

```spl
struct Digest<N>:
    payload: ByteSpan

impl Digest<N>:
    fn len() -> i64:
        self.payload.len()
```

**Error:** `Unknown type: N` (or similar) at the `impl` site.

## Impact

Cannot encode length invariants in the type (e.g. `Digest<32>` for SHA-256,
`Digest<64>` for SHA-512) at compile time.  Callers must enforce length
contracts at runtime.

## Workaround Applied

Fell back to a runtime-length `Digest` struct with no type parameter.
All type safety is enforced at construction time by the caller supplying a
correctly-sized `[u8]`.  Filed in `src/lib/common/crypto/typed/ctypes.spl`.

## Expected Behaviour

`struct Foo<T>: ...` + `impl Foo<T>: ...` should be legal, with `T` in scope
inside the impl body.

## Proposed Fix

Ensure type parameters declared on the struct head are propagated into the
impl block's type environment before resolving member types and return types.
