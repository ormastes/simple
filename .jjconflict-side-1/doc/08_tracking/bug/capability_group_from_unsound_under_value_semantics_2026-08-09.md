# Capability-group `.from()` is unsound as designed: classes are value types

**Filed:** 2026-08-09 (stream P2, unified debug/profile capability feature)
**Affects:** `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md` §3
(and therefore streams P0, P3, P4, P9, P10, P11 which code against it)
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

Design §3 specifies group acquisition as:

> for each group member trait `M`, the source expression must expose an
> accessor returning `Option<M>` ... `Some(group struct bundling both) only
> if ALL members acquire`

Implemented literally (a `DebugProfiler` struct with a `DebugTarget` field
and a `ProfileTarget` field, each filled from `session.debug()` /
`session.profile()`), the group is **silently broken**: driving execution
through the debug half leaves the profile half at zero.

Measured against the P2 ref library before the correction —
`test/01_unit/lib/debug/debug_target_ref_spec.spl`, 70 examples:

```
✗ counts steps EXACTLY over a begin/end window
    assert_equal failed: expected 6, got 0
✗ counts a trapped run's steps up to and including the trap
    assert_equal failed: expected 4, got 0
✗ forwards profiling and yields the same exact step count
    assert_equal failed: expected 6, got -1
Results: 70 total, 62 passed, 8 failed
```

## Root cause

Two independent language facts, both confirmed by a direct probe:

1. **Classes have VALUE semantics.** `val a = Cell.new(); val b = a;
   a.bump()` leaves `b.n == 0`. There is no reference aliasing, so two
   calls to the same `Option<Class>` accessor return two independent
   copies of the same target.
2. **A `fn` trait method receives a COPY of the receiver; only `me`
   mutates.** A mutating method declared `fn` in a trait/impl silently
   discards its mutation — the compiler does not object. This is why the
   design's `me` markers on `set_breakpoint`/`step`/`resume`/`attach`/
   `debug`/`profile`/`shutdown`/`profile_begin`/`profile_end` are
   load-bearing and must be reproduced verbatim by every implementer.

Fact 1 is the fatal one for `.from()`: any group formed by pairing two
`Option<M>` accessors bundles two diverging copies.

## Correction (implemented in P2)

A group is **one trait over one value**, not a struct over two:

- `trait DebugProfiler` is the literal concatenation of `DebugTarget` and
  `ProfileTarget` method sets — which is exactly what the `with` sugar
  desugars to. Nothing added, nothing renamed, so the sugar swap stays a
  pure refactor.
- The implementing type implements all three traits (both members and the
  group), all forwarding to one private implementation.
- Acquisition returns the SINGLE value carrying both capabilities:
  `ref_debug_profiler(session) -> Option<DebugProfiler>`. It still checks
  both member accessors first, so all-or-nothing acquisition semantics are
  preserved exactly.

## Action for P0 (parser/desugar)

`.from()` must be generated to acquire from a single group-typed accessor,
NOT by pairing per-member `Option<M>` accessors. The "match accessor by
`Option<M>` return type" rule in design §3 should become a *capability
check* (all members must be acquirable) followed by a single-value
acquisition. Until the sugar lands, each backend supplies its own
`<backend>_debug_profiler(session)`.

## Action for P3/P4/P6/P8 (backend targets)

A target that must be both debugged and profiled in one scenario has to be
ONE value implementing both traits. Handing a tool a `DebugTarget` from one
accessor and a `ProfileTarget` from another will compile, run, and report
zeros.

## Re-verification 2026-08-17 (fleet lane C, by CONTENT)

STILL-OPEN, matching the doc. `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl`
(453 lines) is a **detector only** — it scans source text for the `G.from(` and `G__from(`
spellings (lines 129, 139, 310-339) and reports them. It does not and cannot change the
`.from()` semantics. Line 375 still records that the corrected single-accessor `.from()` awaits
P0 desugar work. So the doc's statement holds: only the library side ships the corrected
shape, the API itself is unchanged.

This needs the design correction the doc calls for, not a lint patch. No patch attempted.
