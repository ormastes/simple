# expect(a == b).to_equal(false) comparison-matcher footgun

**Date:** 2026-07-17
**Status:** PHASE-1 SWEPT — parse-aware transformer rewrote 1,386 simple cases in 321 files (2026-07-17); ~1,360 complex lines remain flagged by the checker

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
