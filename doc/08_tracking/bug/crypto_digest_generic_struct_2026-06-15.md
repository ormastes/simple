# Bug: Generic struct type parameter not resolved in impl block

**ID:** crypto_digest_generic_struct_2026-06-15
**Date:** 2026-06-15
**Severity:** P2 (language limitation, workaround exists)
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
