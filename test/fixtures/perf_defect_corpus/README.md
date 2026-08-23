# Perf/memory defect corpus

Deliberately-defective sample code, one file per class, each paired with a
near-identical **correct** file. Tracked in git so the corpus is reviewable and
durable; **never scanned** by the ratchets, lint sweeps, or the offender census.

## Why it must not be scanned

These files are debt on purpose. If a scanner swept them they would pollute
every baseline and offender count, and a ratchet that counts its own fixtures as
debt is broken.

## How the exclusion works — by construction, not by allowlist

`scripts/check/check-cow-alias-hotpath.shs` scans exactly two roots:

```sh
SRC="$ROOT/src/compiler"
LIBSRC="$ROOT/src/lib"
```

`test/fixtures/` is not under either, so the exclusion is structural. There is no
allowlist entry to rot, and no flag that could accidentally widen the scan. The
same holds for the whole-tree offender census, which enumerates `src/**`.
`test/fixtures/` is additionally named as categorically ineligible for spec
scope in the bootstrap phase-gating rules, and none of these files is a
`*_spec.spl`, so the test runner does not execute them either.

**Do not "helpfully" re-include this directory in a scan root.** If you widen a
scanner's root, exclude `test/fixtures/perf_defect_corpus/` explicitly in the
same change.

Proof recorded 2026-08-23: with all 10 fixtures present on disk,
`sh scripts/check/check-cow-alias-hotpath.shs` reports
`PASS — 9681 file(s) scanned, 191 offender(s) checked, 0 new, 0 stale` — byte
for byte the same verdict as before the corpus existed.

## Why pairs

A rule that fired on everything would pass every positive and fail every
negative. The pair is what proves the rule DISCRIMINATES. Keep each file
minimal and to a single defect — lint cost is superlinear in file content and
`sh scripts/check/check-lint-cost-budget.shs` is fail-closed.

## Detection matrix

Executable and asserted in
`test/01_unit/compiler/lint/perf_defect_corpus_detection_spec.spl` (11 examples).
Classes that are NOT detected assert **zero** findings, so a future rule that
starts catching one turns the spec red and forces this table to be updated
rather than silently drifting.

| class | fixtures | detected | diagnostic actually emitted |
|---|---|---|---|
| COW round trip | `cow_roundtrip_{positive,negative}.spl` | **yes** | `warning[PERF-COW-001]: COW round trip: `self.table` is taken into local `t`, mutated, and stored back (in `add`)` |
| COW by-value helper | `cow_byvalue_{positive,negative}.spl` | **yes** | `warning[PERF-COW-002]: COW by-value helper: `self.xs` is passed by value and stored back (in `add`)` |
| `keys()`/`values()` in loop | `cow_keysinloop_{positive,negative}.spl` | **yes** | `warning[PERF-COW-003]: keys()/values() on loop-invariant receiver `self` inside a loop body (in `walk`)` |
| per-character walk (CHARWALK) | `charwalk_{positive,negative}.spl` | **no — deliberately** | none |
| unbounded memory retention | `memory_retention_{positive,negative}.spl` | **no — not statically detectable** | none |

Every negative fixture emits no perf diagnostic, verified through the real CLI
(`bin/simple lint <file>`), not only through the rule function.

## Why the two undetected classes are not "just missing a rule"

**CHARWALK** (an interpreted `substring(i, i+1)` per character with no native
fast reject, the shape commit `8d3b7d009b9` removed). The identical loop is
correct and unavoidable wherever a character genuinely must be classified one at
a time — this repo's own lint helpers do it — so a rule on the shape alone fires
on every correct use. Discriminating needs to know whether a native scan could
have replaced the loop, a dataflow question a text lint cannot answer. It stays
pinned by mechanism in `scripts/check/check-perf-regression-tests.shs`
(CHARWALK rows) instead.

**Unbounded memory retention.** Every line of `memory_retention_positive.spl` is
individually correct: the accumulator is mutated through its owner, no COW alias,
no quadratic loop. Whether the growth is bounded is a LIFETIME property of a
whole run — it depends on how much the caller feeds in and whether any consumer
releases — and the source shape is identical to every legitimate builder. The
positive and negative fixtures are *indistinguishable to any source lint*, which
is exactly why both assert zero. Detection belongs to a runtime RSS budget. See
`doc/08_tracking/bug/native_build_worker_rss_unbounded_953mb_from_oom_kill_2026-08-23.md`
(peak 2.77 GiB, still climbing ~40 MB/s, ~953 MB below the earlyoom kill).

## Adding a class

1. Add `<class>_positive.spl` and `<class>_negative.spl` here, minimal, one
   defect each, with a header comment saying what the shape costs.
2. Add a `describe` block to the detection spec asserting the real outcome —
   including zero, if the class is not caught.
3. Re-run `sh scripts/check/check-cow-alias-hotpath.shs` and confirm its
   file/offender counts are unchanged. An exclusion you did not verify is an
   exclusion that does not exist.
