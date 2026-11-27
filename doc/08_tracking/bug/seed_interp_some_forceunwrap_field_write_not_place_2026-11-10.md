# Seed interpreter cannot write through explicit Some/Ok force unwrap

Bug: seed_interp_some_forceunwrap_field_write_not_place_2026-11-10 (P1).
Status: source repair implemented; executable verification pending (TEST_BLOCKED).

The bootstrap seed interpreter accepts `item!.n` reads but rejects writes when
item contains `Some(Cell(...))` or `Ok(Cell(...))`. An implicit nullable Cell
works. This blocks opt-in compiler source-authority tracing, which creates the
trace and cost owners as explicit Some(class) values.

## Original evidence

The 256-source-file private Git fixture from p1_seed_startup executes
compiler_source_authority_acquire_v1 with SIMPLE_INVENTORY_TRACE_ATTEMPT set.
It fails after phase=authority with `invalid assignment: field assignment target
is not a place`. Trace-disabled control on the same fixture returns valid=true,
reason=ok in8.774709s (process9.91s), exit0.

Minimal source:

```simple
class Cell:
    n: i64
fn main() -> i64:
    var item: Cell? = Some(Cell(n: 4))
    item!.n = 5
    if item!.n == 5: 0 else: 1
```

Deployed Nov4 seed SHA256
8c7341592f4d47ded4a0603347cf972e344a3fd075444a8004afcae94917741c:
implicit nullable write PASS; explicit Some field write exits1 with the error.
Nov9 bootstrap seed SHA256
2d73aceec77f28740d95d194c43c80f4d892308d4d1101a69d6b4e9d3a899f59:
explicit Some field write exits1; Some and Ok augmented writes exit1 with
`augmented assignment to a missing place`; Some mutating-method control PASS.
These are bootstrap-seed diagnostics, not self-hosted product test evidence.

Retained commands, standalone fixtures, and logs are in coordinator
build/bug-campaign/p1_enum_opt/forceunwrap_*.

## Mechanism and repair

src/compiler_rust/compiler/src/interpreter/place.rs resolves ForceUnwrap by
returning the inner place unchanged. That correctly handles direct nullable
objects but loses the payload traversal for explicit Option/Result wrappers.
The read evaluator already unwraps those payloads, so read and write disagree.

Retain Projection::Unwrap in the writable path. Read/mutable steps navigate
canonical Some/Ok payload storage; None/Err/nil and missing payloads have no
writable location. Direct nullable objects and user enums retain identity.
Store-back retains wrappers, copy-on-write values preserve isolation, and
shared ClassInstance payloads retain identity. The final-projection consumer explicitly handles unwrap, and the class-array mutation fast path follows unwrap without falling back to copying. Index detection also traverses
ForceUnwrap to preserve index evaluation order.

## Required verification

- Actual-owner Rust tests exercise payload traversal, absence and malformed
  values, nested wrappers, direct-value identity, COW aliases, shared classes,
  and resolver/index behavior.
- Interpreter integration runs the original field/augmented/nested/indexed
  grammar and mutating-method control with eight value assertions.
- Rebuilt bootstrap seed must run the original 256-file trace-enabled source
  authority reproducer; keep the trace-disabled prior control scoped to its
  unchanged inputs.
- Full crate and applicable compiler smoke gates remain required. No test or
  bootstrap PASS is claimed from the source draft or parser acceptance alone.

Provider token input/output/cache usage, cohort average and ratio: unavailable.
No values are guessed and no zero-filled usage is claimed.

Interim checks: Rust parser accepted the repair draft; a reduced-carrier borrow/type-shape check compiled the exact new helper functions. Neither executes the product. The full original-form integration fixture remains RED on the unpatched Nov9 seed.
