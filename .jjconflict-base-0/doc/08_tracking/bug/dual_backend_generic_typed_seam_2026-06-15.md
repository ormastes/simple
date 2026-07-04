# Bug: generic fn over trait bound fails for typed dual-backend seam

**ID:** dual_backend_generic_typed_seam_2026-06-15
**Filed:** 2026-06-15
**Severity:** P2 — language expressiveness gap (workaround exists: Seam A non-generic helpers)
**Component:** compiler / generics

## Summary

Attempting a generic typed alpha runner `fn dual_backend_run_typed<T: ByteEq>(...)` fails
with "Unknown type: T" in the interpreter. This is a different manifestation from the
generic-struct bug (`crypto_digest_generic_struct_2026-06-15`): that bug is about type
parameters on *struct definitions*; this bug is about type parameters on *fn signatures*
with trait bounds.

## Minimal repro

```simple
# probe_generic_fn_trait_bound.spl
trait ByteEq:
    fn to_bytes() -> [u8]

struct Foo:
    data: [u8]

impl Foo:
    fn to_bytes() -> [u8]:
        self.data

fn run_typed<T: ByteEq>(a: T, b: T) -> T:
    a

fn main():
    val f = Foo(data: [1u8, 2u8])
    val result = run_typed(f, f)
    print(result.to_bytes().len().to_text())
```

**Error observed when run via `bin/simple run`:**
```
Unknown type: T
```

## Root cause hypothesis

The type inference / monomorphisation pass does not instantiate `T` in the fn signature
body when the call site is resolved. The same "Unknown type: Id" root as the struct
generic case.

## Impact

Cannot write a single generic seam helper `dual_backend_run_typed<T: ByteEq>` that
works over all crypto custom types (Digest, MacTag, ByteSpan-backed types).

## Workaround

Seam A: write separate non-generic helpers per output type (`alpha_run_digest`,
`alpha_run_span`). Landed in `src/lib/common/crypto/typed/seam.spl`.

## Related

- `doc/08_tracking/bug/crypto_digest_generic_struct_2026-06-15.md` — generic struct params
- `doc/08_tracking/bug/generic_type_alias_parse_reject_2026-06-10.md`
