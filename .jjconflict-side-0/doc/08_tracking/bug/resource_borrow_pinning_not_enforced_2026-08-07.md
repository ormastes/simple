# `resource` invariant 3 (borrow pinning across foreign calls) is not enforced

**Status:** ARCHITECTURAL-OPEN (final terminal-status pass 2026-08-10:
re-read `record_move` at `src/compiler/55.borrow/borrow_check/borrow_graph.spl:533`
— still only checks `self.moved_now`, no consultation of `borrows_of`/
`has_conflicting_borrow` in either direction; no borrow-liveness/region
infrastructure or foreign-call marker exists anywhere in `55.borrow/` or
`50.mir/`. Genuinely requires a multi-week subsystem addition per the WP-G
scope note below, not a local fix — left OPEN and unmodified). Filed by
WP-G (`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`),
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

## Re-verification (2026-08-09, parallel bug-list pass)

Re-checked against the standing "borrow checker is architecturally limited"
pattern noted elsewhere in this repo (borrow_check today runs only in the
AOT/JIT/VHDL pipelines, not universally — see
`doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
and related notes on `borrow_check` pipeline coverage). This item is a
**distinct but related** architectural gap: even where `borrow_check` DOES
run, it has no borrow-liveness/region infrastructure and no foreign-call
marker, so invariant 3 cannot be enforced by any local fix to `record_move`.
Building region/lifetime tracking plus a foreign-call-boundary marker is a
genuine subsystem addition (est. multi-week), not a bug-fix-sized change, and
is explicitly out of scope for a single-item pass per the standing guidance
not to attempt a half-built version of a borrow-checker rewrite.

**Confirmed: still OPEN, still architectural.** No code changed in
`55.borrow/` or `50.mir/` in this pass. Left as-is per the doc's own
"Unblock condition" below.

## Unblock condition

A borrow-liveness/region pass (item 1 above) plus a foreign/SFFI call marker
(item 2) land in `55.borrow`/`50.mir`; then `record_move` (or the Drop arm)
gains a "does this place have a live outstanding borrow" check before
allowing the move/drop, and the RED spec above should be updated to assert
`errors.len() > 0` passes for real (it already does — no change to the
assertion needed, only to the implementation).

## Content re-verification 2026-08-17 (m4_compiler_spl lane) — STILL OPEN

The central claim holds verbatim against current source.
`BorrowGraph.record_move` (`src/compiler/55.borrow/borrow_check/borrow_graph.spl:580-608`)
iterates **only** `self.moved_now` and emits `borrowerror_use_after_move` on a
conflict. It never calls `get_or_create_borrows(point)` and never consults
`borrows_of(place)`, so moving a place that is currently borrowed produces no
diagnostic at all — the borrow is not pinned.

The asymmetry is visible in the same struct: `record_assign` (`:609-643`) DOES
take `val conflicts = borrow_set.borrows_of(place)` (`:631`) and reports
`"Assignment while mutably borrowed"`. Only the move path is missing that
consultation. `borrows_of` has exactly two references tree-wide
(`borrow_graph.spl:380` definition, `:631` sole call site).

What has landed since this doc was filed is adjacent but different: LANE ISO1's
double-*move* detection (`:600-604`, documented in `record_move`'s own
docstring) and WP-G's Drop-as-Move arm (`borrow_check/mod.spl:245-273`). Both
extend move-vs-move; neither adds move-vs-borrow.

**Verdict: ARCHITECTURAL-OPEN, unchanged.** No fix attempted here: adding a
borrow consultation to `record_move` changes checker verdicts tree-wide, and
the accepted over-approximation already recorded in `mod.spl:265-272` (the walk
is linear over `func.blocks`, not CFG-path-sensitive) means it would false-
positive on mutually exclusive branches without region/liveness infra first.

### Execution: the named reproducer is GREEN, and that is the alarming part

`bin/simple test test/01_unit/compiler/resource/resource_borrow_pinning_spec.spl
--timeout 900` under `scripts/resource/test-slot.shs` eventually completed
(rc=0, ~50 min wall at load 48-124 — an earlier reading of this same run as a
"zero-byte log" was my polling racing the output flush, and is retracted):

    SPEC FILE VERDICT: .../resource_borrow_pinning_spec.spl declared>=1 executed=1 passed=1 failed=0 dropped=0
    Results: 1 total, 1 passed, 0 failed

The spec's own docstring says this `it` block "is expected to FAIL until the
borrow-liveness-vs-move-or-drop check described above is implemented", and its
assertion is an honest statement of the DESIRED behaviour:

    assert_true(checker.errors.len() > 0)

So a spec written to be RED against this gap is now GREEN **while the gap it
describes is still present in the source** (`record_move` still never consults
`borrows_of` — see above; that is a direct read of the file, not an inference).

This does not close the bug. The likely explanation is that the assertion does
not discriminate: it counts ANY entry in `checker.errors`, not the invariant-3
diagnostic. The hand-built fixture declares `locals: []` while referencing
`LocalId(id: 0)` and `LocalId(id: 1)`, so an unrelated out-of-range-local error
would satisfy `errors.len() > 0` just as well as the borrow diagnostic would —
a false green of exactly the silent-pass class this sweep exists to find.

**Unproven either way:** I did not capture the error MESSAGES, so I cannot say
which error made the count non-zero. Deciding it needs one more run printing
`checker.errors`, at ~50 min on this host.

**Recommended next step (not taken here):** tighten the assertion to match the
diagnostic text rather than the count, then re-run. I deliberately did not edit
the spec: turning it red-or-green again without being able to re-verify inside
this session would ship an unverified test change, which is worse than leaving
an honest note.
