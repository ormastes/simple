# Bug: generic fn over trait bound fails for typed dual-backend seam

Status: **CLOSED — DID NOT REPRODUCE** (2026-08-17, wave_01 lane B, reproduce-first)
Previous line "Status: OPEN (P2), re-verified 2026-08-17 by source inspection" was a
SOURCE-INSPECTION verdict only; it was never re-run. It is superseded by execution below.

## 2026-08-17 re-run — the documented minimal repro is GREEN

The "Minimal repro" block below was extracted verbatim and executed against the
deployed seed (`bin/simple`, Rust seed):

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe_generic_fn_trait_bound.spl
rc=0
2
```

`2` is the correct answer. No `Unknown type: T`. Three variants all print `2`:
the verbatim repro (bare `impl Foo:`), the corrected `impl ByteEq for Foo:`, and a
multi-letter type-parameter variant (`<Elem: ByteEq>`) added to check that the fix is
not a single-letter special case.

**Content evidence (not SHA ancestry).** The `Unknown type: {type_name}` text is
raised only from `src/compiler_rust/compiler/src/hir/lower/error.rs:22`, at three
sites in `hir/lower/type_resolver.rs` (40, 269, 435). Type-parameter names no longer
reach any of them:

- `type_resolver.rs:167-169` — a bare single-uppercase-letter name resolves to
  `TypeId::ANY` before the `UnknownType` arm at 269 is reachable.
- `type_resolver.rs:264-267` — `lenient_types` mode returns `TypeId::ANY` for any
  unresolved name, which covers the multi-letter case.

`src/compiler/40.mono/instantiation.spl` (the file this row was filed against) is 87
lines and contains no `Unknown type`, `trait_bound`, or `type_param` handling at all —
it was never the site of this defect.

### Separate, still-live observation (NOT this bug — do not reopen this doc for it)

Under the DEFAULT engine (JIT, no `SIMPLE_EXECUTION_MODE`) both variants abort with
SIGILL (rc=132, core dumped), not with a type error:

- verbatim repro (`impl Foo:`, no `impl Trait for`):
  `runtime error: duck-typed virtual method call (trait has no `impl Trait for ...` in
  unit; no vtable)` — already filed as `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`.
- corrected repro (`impl ByteEq for Foo:`): `runtime error: invalid field receiver`.

Both are loud crashes in the seed JIT (backend lane), not silently wrong results, and
the JIT/backend is owned by another lane. The second one does not obviously match an
existing doc; whoever owns the backend lane should confirm coverage.

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

## Verification 2026-08-17 (w0001 compiler_spl lane)

Re-reproduced against the deployed seed `bin/simple`. **The doc's framing is wrong:
the defect is not generics and not trait bounds.** Four minimal fixtures:

| fixture | result |
|---|---|
| `fn pick<T>(a: T, b: T) -> T` called with i64 | **PASS** — `v=3` |
| plain `struct` field read `b.n` | **PASS** — `n=3` |
| inherent `impl Blk: fn size2(self) -> i64: self.n` | **PASS** — `s=3` |
| `impl T2 for Blk` whose method body returns a constant (no `self.` read) | **PASS** — `k=7` |
| `impl Sized2 for Blk: fn size2(self) -> i64: self.n` | **CRASH** |

Failing case output:
```
runtime error: invalid field receiver
Illegal instruction (core dumped)   # rc=132
```

Narrowed root cause: **a TRAIT-impl method that reads `self.<field>` fails to bind
`self` to the receiver struct**; the identical body inside an INHERENT `impl`
works. Generic type parameters and trait bounds are both innocent — a generic fn
with no trait impl involved runs correctly.

Notes for whoever picks this up:
- This is a LOUD crash (rc=132, SIGILL), not a silent wrong result, so it does
  not belong to the silently-wrong-results batch this lane was scoped to.
- It is in the Rust seed interpreter, **not** in `src/compiler/40.mono/instantiation.spl`
  as the row's `file` column claims. `instantiation.spl` (87 lines) is a name-mangling
  + cache facade and contains no `self`-binding logic.
- No fix attempted here: the code is outside this lane's slice
  (`src/compiler/**.spl`). Re-file against the interpreter's field-access path.
