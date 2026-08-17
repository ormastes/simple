# expect(a == b).to_equal(false) comparison-matcher footgun

**Date:** 2026-07-17
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Symptom

Spec files assert comparisons indirectly: `expect(a == b).to_equal(false)`,
`expect(a != b).to_equal(true)`, and `.to_be(...)` variants. This shape has
two problems:

1. It routes a comparison result through the expect/bool channel, which has
   a history of tag-box/narrowing landmines (see the text-eq bool-narrowing
   fix in 58b24c224bb and the `.?`-on-0-i64 quirk) — an assertion can pass
   vacuously or invert under the wrong lowering.
2. On failure it reports `expected true, got false` with no operand values,
   hiding the actual mismatch.

Direct forms are strictly better: `expect(a).to_equal(b)` /
`expect(a).to_not_equal(b)`, or `assert_true(...)`/`assert_false(...)`
(defined in `src/lib/nogc_sync_mut/spec.spl`) for genuinely compound
conditions.

## Prevention (landed)

`scripts/check/check-expect-footgun.shs` — POSIX sh/awk scanner that flags
the pattern across `test/` and `src/**/*_spec.spl` (excludes generated
`doc/06_spec/`, `vendor/`, mirrors). `--strict` exits 1 on any hit for gate
use. Counts at time of writing: ~1,800 hits across ~477 files.

## Sweep attempt — REVERTED (2026-07-17)

A regex/Perl bulk transformer was applied across 477 spec files and
**destroyed assertions instead of rewriting them**: aggregate diff was
+6,254/−7,035 lines (net −781), with 11 files suffering pure deletions
(e.g. `cli_native_build_main_contract_spec.spl` lost two unrelated
`.to_contain(...)` assertions outright). No per-file test verification had
been run. The coordinator restored all 474 damaged files from origin
verbatim; only this doc and the checker were kept.

**Lesson / requirement for the redo:** the rewrite must be parse-aware
(balanced-paren operand extraction, not line regex), must not touch
non-matching lines, and must be verified per file (spec run before/after,
or at minimum an assertion-count invariant: rewritten file has the SAME
number of expect/assert statements as the original). Note the current
verification environment is constrained: deployed `bin/simple` has the
stale `rt_cli_arg_count` gap and the seed cannot parse the pure-Simple
compiler tree (f-string-as-argument grammar gap), so lib-level specs are
the practical verification set.

## Remainder

Full current hit list: run `sh scripts/check/check-expect-footgun.shs`.

## Phase-1 sweep (landed, 2026-07-17)

Redone with a parse-aware transformer (balanced-paren operand extraction,
single top-level comparator required, top-level and/or/not excluded,
single-line matches only). Rewrites: positives -> `expect(A).to_equal(B)`;
negatives -> `assert_not_equal(A, B)` only where the file imports
`use std.spec.*` (else left for phase 2). Per-file invariants enforced:
line count unchanged, expect+assert count unchanged, only matched lines
touched. Post-apply audit: every changed line in all 321 files conforms to
the expected before/after patterns vs origin (0 files excluded).
Behavioral spec runs are blocked by the documented tooling walls (stale
deployed binary's rt_cli_arg_count gap; seed runner cannot compile the
pure-Simple test-runner) — A/B confirmed the failure is byte-identical for
origin and swept content, i.e. pre-existing and unrelated. Remaining
~1,360 complex lines: run the checker for the current list.

## 2026-08-17 — the GATE itself was fail-open (fixed)

Classified by CONTENT, not SHA ancestry. Row verdict: **LIVE**, but the live
defect was not the remaining ~1,360 spec lines — it was the checker.

### Reproduced RED (before any change)

`scripts/check/check-expect-footgun.shs` computed only a HIT count. It never
counted the FILES it fed to `grep`, so a scan of ZERO files was byte-identical
to a clean tree, and exited 0 — in BOTH lanes, because `--strict` shared the
same early `exit 0` at line 80-82:

```
# empty fixture tree (0 spec files present)
$ sh check-expect-footgun.shs           -> rc=0  "EXPECT-FOOTGUN: No footgun patterns found"
$ sh check-expect-footgun.shs --strict  -> rc=0  "EXPECT-FOOTGUN: No footgun patterns found"
```

Identical text and exit status to a genuinely clean tree. Absence of evidence
reported as evidence of absence — the exact fail-open shape catalogued in
`gate_oracle_soundness_census_2026-08-11.md`. The gate also had no `--selftest`
and no `PASS/FAIL/ERROR` verdict line, so nothing pinned the behaviour.

Root cause: `scripts/check/check-expect-footgun.shs:54-82` (pre-fix) — `COUNT`
was the only oracle; the input cardinality was never computed.

### After

Repo guard convention, verdict always the last line of stdout, non-vacuity
absolute (0 files scanned is ERROR, never a pass), fatal `--selftest`
(3 fixtures: dirty must detect, clean-non-empty must pass with n>0, empty tree
must yield 0 scanned so the caller is forced to ERROR).

```
$ sh check-expect-footgun.shs --selftest   rc=0  PASS -- 3 selftest fixture(s) checked, 0 failures
$ sh check-expect-footgun.shs (empty tree) rc=2  ERROR -- nothing was checked (0 spec files found ...)
$ sh check-expect-footgun.shs              rc=0  WARN -- 20580 file(s) scanned, 2531 footgun pattern(s) found (report-only; use --strict to fail)
$ sh check-expect-footgun.shs --strict     rc=1  FAIL -- 20586 file(s) scanned, 2531 footgun pattern(s) found
```

The empty-tree case moved from `rc=0` to `rc=2` — that is the fix.

### Similar-problem detection gate (new)

`scripts/check/check-scan-guard-vacuity.shs` generalises to the CLASS rather
than this one script: every `check-*.shs` under `scripts/check/` that walks a
corpus (`find` / `git ls-files` / `grep -r`) must have BOTH a non-vacuity oracle
(a zero-input path reaching `exit 2`) and a COUNTED success verdict. Ratcheted
against `scripts/check/scan_guard_vacuity_baseline.txt`; FAILs on any newly
fail-open guard AND on any baselined entry that now passes (stale baseline).
Fatal `--selftest`, 6 fixtures, including a byte-level replay of this incident's
shape and an empty-tree fixture that must classify zero scripts.

### Not fixed here

The remaining 2,531 flagged spec lines are unchanged — this change makes the
count honest and makes `--strict` capable of failing, it does not sweep phase 2.
