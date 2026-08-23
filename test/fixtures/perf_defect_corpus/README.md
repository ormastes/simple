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

## Cross-implementation check (pure Simple <-> Rust seed)

A defect class usually exists in both halves. Each row states which
implementation the fixture exercises and the verdict on the other half — twin
found, or twin verified absent WITH the evidence. Where the twin is Rust-side,
the pin is the existing mechanism row in
`scripts/check/check-perf-regression-tests.shs`, not a `.spl` fixture: this
corpus is `.spl` and the rule that reads it is a `.spl` linter, so a Rust
fixture here would be undetectable by construction and would only look like
coverage.

| class | fixture exercises | twin in the other half? |
|---|---|---|
| COW round trip / by-value / keys-in-loop | pure Simple **source shape** | **Twin FOUND, already fixed and pinned, and it is a different shape.** Rust `Vec` has no copy-on-write, so the source shape cannot occur in the seed. The seed's twin is shape (d) of the class — an *interpreter-created* temporary where the `.spl` source looks correct — in `handle_method_call_with_self_update` (`src/compiler_rust/compiler/src/interpreter/interpreter_helpers.rs`, used from `interpreter_eval.rs:1512` and `interpreter/block_exec.rs:22`). Measured and fixed: distinct backing buffers over a 2,000-push loop went 1321 -> <64. It is pinned by runtime buffer-identity mechanism tests, not by a lint, because no source lint can see it. |
| CHARWALK per-character walk | pure Simple **source** (`lint_text.spl`, `raw_rt_access.spl` — the files the CHARWALK rows pin) | **Twin verified ABSENT.** `grep -rn "lexical_code_lines" src/compiler_rust --include=*.rs` returns **zero hits**: this lint text-walking machinery exists only in pure Simple, so there is no seed counterpart to regress. |
| Unbounded memory retention | pure Simple fixture, but the **measured defect is Rust-seed-side** | **Twin FOUND on the Rust side and it is the primary one** — `parsed_imported_module` in `src/compiler_rust/compiler/src/hir/lower/import_loader.rs` plus `module_cache.rs` (the IMPORTASTMEMO rows). **The pure-Simple twin is verified ABSENT with evidence:** `grep -rn "parsed_imported_module\|IMPORTED_MODULE_AST" src/compiler --include=*.spl` returns zero hits, and the pure-Simple import path (`10.frontend/core/interpreter/module_loader_resolve.spl:33-34`) caches resolved **paths** — short strings, one per module — not parsed ASTs, and exposes an explicit `module_resolve_cache_reset()`. Different magnitude, different object, bounded, and clearable. |

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
