# `resource` invariant 3 (borrow pinning across foreign calls) is not enforced

**Status:** OPEN. Filed by WP-G (`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`),
resource-ownership campaign. Architecture reference:
`doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`
§8, invariant 3: "Borrow pinning: a borrowed resource stays live through the
entire foreign call, including blocking calls."

## What's missing

`BorrowGraph.record_move` (`src/compiler/55.borrow/borrow_check/borrow_graph.spl`,
~line 533) checks only `self.moved_now` before recording a move. It never
consults the borrow set (`borrows_of`/`has_conflicting_borrow`, the exact
functions `record_borrow` itself uses at line ~501 to reject a NEW borrow of
an already-moved place). The reverse check — rejecting a move/drop of a place
that has an outstanding, still-live borrow — has no code path anywhere in the
checker. WP-G's own new `Drop` arm (`borrow_check/mod.spl`, this session)
reuses `record_move`, so it inherits this same gap: dropping/closing a
resource while a `Ref` borrow of it is outstanding is not flagged.

Separately, there is no MIR-level or checker-level concept of "this call is a
foreign/blocking call whose duration a borrow must span" at all. Grepping
`borrow.pin`/`pinning`/`BorrowPin`/`foreign_call_borrow` across `55.borrow/`
and `50.mir/` returns zero hits (verified 2026-08-07). `MirInstKind.Call` /
`MirTerminator.CallTerminator` carry no "this argument must outlive the call"
marker, and nothing distinguishes a foreign/SFFI call from an ordinary Simple
function call at MIR level either.

## What real enforcement would need

1. A call-scoped borrow-liveness region: a borrow created for a call argument
   must stay live for the callee's WHOLE execution (not just the call
   instruction's own program point) — genuine region/lifetime infrastructure,
   not a single new instruction-kind arm.
2. A way to identify which calls are foreign/blocking (SFFI calls
   specifically) so the rule only fires where the architecture doc requires
   it — ordinary Simple-to-Simple calls are not in scope for this invariant
   as worded.
3. `record_move`/the new `Drop` arm would then need to consult that borrow
   region before allowing a move/drop, mirroring `record_borrow`'s existing
   "would this new borrow conflict with an already-moved place" check but in
   the opposite direction.

None of this exists today. Building it was explicitly out of scope for WP-G
per that WP's own boundary ("do NOT attempt a half-built version ... leave it
RED, file a bug record").

## Proof: RED spec

`test/01_unit/compiler/resource/resource_borrow_pinning_spec.spl` — hand-
built MIR (`Ref` borrow of a place immediately followed by `Drop` of the same
place, standing in for a resource released before the foreign call it was
passed to could plausibly have completed). Real run:

```
Results: 1 total, 0 passed, 1 failed
```

The single `it` asserts `checker.errors.len() > 0` (the invariant-3-respecting
outcome); the measured actual is 0, so it fails exactly as expected. Left RED
per this session's standing practice — the assertion states the DESIRED
behaviour, not a weakened match to the current gap.

## Unblock condition

A borrow-liveness/region pass (item 1 above) plus a foreign/SFFI call marker
(item 2) land in `55.borrow`/`50.mir`; then `record_move` (or the Drop arm)
gains a "does this place have a live outstanding borrow" check before
allowing the move/drop, and the RED spec above should be updated to assert
`errors.len() > 0` passes for real (it already does — no change to the
assertion needed, only to the implementation).
