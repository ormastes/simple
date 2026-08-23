# Lint rule: COW-alias hot path (`PERF-COW-001/002/003`)

**Added:** 2026-08-23 · **Severity:** warning · **Rule name:** `cow_alias_hotpath`
**Implementation:** `src/compiler/35.semantics/lint/cow_alias_hotpath.spl`
**Wired at:** `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` (`check_cow_alias_hotpath_spl`)
and the code→rule-name map in `_LintMain/config_and_model.spl`.
**Specs:** `test/01_unit/compiler/lint/cow_alias_hotpath_spec.spl`,
`test/01_unit/compiler/lint/cow_alias_hotpath_product_fixes_spec.spl`

## What it catches

Simple has value semantics implemented as copy-on-write. A collection is an
Arc-backed container and a mutation goes through `Arc::make_mut`, which
deep-copies the WHOLE container whenever the Arc is aliased. That is correct —
two live bindings must not observe each other's writes — but catastrophic when
the alias is an accidental temporary the code never needed: the copy then fires
on EVERY write and building an n-element collection costs O(n²).

| code | shape | correct form |
|---|---|---|
| `PERF-COW-001` | `val t = self.f` … `t.push(x)` … `self.f = t` | `self.f.push(x)` |
| `PERF-COW-002` | `self.xs = helper(self.xs, v)` | mutate `self.xs` in place |
| `PERF-COW-003` | `.keys()` / `.values()` on a **loop-invariant** receiver inside a `while`/`for` body | hoist the call above the loop |

`PERF-COW-003` deliberately exempts a receiver that is **rebound each
iteration** (`for surface in …` then `surface.callables.keys()`, or a `val`
declared inside the loop body). Each such materialization is of a *different*
dict, every key is visited once, and the total is O(total entries) — optimal.
Flagging those was a measured false positive.

## Relationship to the push-time ratchet

`scripts/check/check-cow-alias-hotpath.shs` freezes the existing population of
these shapes and blocks additions at push time, but it scans **`src/compiler/**`
only**. This lint reports the same three shapes at **authoring** time over every
file the linter is pointed at. Detection semantics are deliberately identical,
and the spec's acceptance cases are lifted from the ratchet's own selftest
fixtures — including both of its documented false-positive fixes (per-function
state reset, loop-varying receiver) — so the two cannot disagree.

Cross-validated 2026-08-23: over `src/compiler/**` the lint reports exactly the
same 7 offenders the ratchet baselines, and over the 191 `src/lib` rows the
baseline also covers, the two agree row for row. The lint additionally finds
101 offenders in `src/app`, `src/os` and `src/compiler_rust` — roots the ratchet
never scans.

## Severity

`LintLevel.Warn`, never `Deny`, matching the `RAW-RT-00x` / `LEADOP001`
precedent: a rule is not escalated before its population is converted. The
remaining population is tracked in
`doc/08_tracking/bug/cow_alias_hotpath_lint_findings_backlog_2026-08-23.md`.

## Cost

The rule is one linear pass over the file's code lines, no AST. Measured
2026-08-23 on this (loaded) box: 15,213 `.spl` files scanned in 81 s ⇒ ~5 ms per
file, against a lint invocation whose fixed startup alone is 8–12 s. An
interleaved A/B of `bin/simple lint` on one real file over three pairs gave
on = 11.94 / 15.20 / 19.06 s and off = 12.11 / 16.52 / 17.21 s — the rule's cost
is indistinguishable from box noise. `sh scripts/check/check-lint-cost-budget.shs`
stays green: `PASS — 1 fixture(s) checked, lint completed in 15s of a 240s budget`.

## Ratchet interaction found while landing this rule

Two things surfaced when the ratchet was re-run over the fixed tree, both
recorded rather than smoothed over:

1. **The ratchet does not treat `me ` as a function boundary** (its awk resets
   on `fn `/`pub fn ` only), so its offender labels carry the wrong enclosing
   function name for methods — e.g. all seven `interpreter_types.spl` rows were
   attributed to `_stored_env_id_equals`. This lint does reset on `me`. The
   labels are cosmetic and the ratchet was deliberately left alone, but do not
   trust its `fname` field for a method.
2. **The ratchet matches `.keys()` inside string literals** (it excludes only
   whole-line `#` comments), so spelling the method names in full inside this
   rule's own diagnostic text made the rule a false offender in the ratchet's
   scan. The message therefore omits the leading dot, with a comment saying why.

The baseline was regenerated once, as a reviewed update: the diff is exactly the
seven `interpreter_types.spl` rows this change fixed (198 -> 191 offenders), a
strict tightening. `PASS — 9681 file(s) scanned, 191 offender(s) checked, 0 new,
0 stale`.

## Detection corpus

`test/fixtures/perf_defect_corpus/` holds a durable, tracked, deliberately-
defective sample for every perf/memory class, each paired with a near-identical
correct file, plus its own README. It is excluded from every scanner **by
construction** (the ratchet's roots are `$ROOT/src/compiler` and `$ROOT/src/lib`;
`test/fixtures/` is under neither), verified by re-running the ratchet with all
fixtures present and getting a byte-identical verdict. The matrix is executable:
`test/01_unit/compiler/lint/perf_defect_corpus_detection_spec.spl` (11 examples)
asserts what is caught AND asserts zero for the two classes that are not, so a
future rule cannot start catching one without turning the spec red.

## Known limits

- Text heuristics, not dataflow: a round trip whose take and store-back are
  split across two functions is not detected (by design — the ratchet's
  `crossfn` fixture pins that as a must-NOT-flag).
- Shape (d) from the analysis doc — an interpreter-created temporary, where the
  `.spl` source looks correct — is invisible to any source lint. It is covered
  by the runtime buffer-identity mechanism tests instead.

Background: `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`
