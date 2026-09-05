# sspec-maintain scorer: three loopholes let ceremony score as substance (var tautology, trailing-comment tautology, comment-line evidence) + one false positive (MNT-009 punctuation)

**Date:** 2026-09-05
**Status:** FIXED in `src/app/sspec_maintain/source_facts.spl` (same day); specs below
**Severity:** scoring integrity — an anti-tautology BLOCKER was one keyword from inert
**Found by:** the plan-acceptance lane (six agents writing 36 specs) reporting the
dodges they used; measured with `scripts/check/sspec-score-seed-lane.shs`

## Symptoms (all measured on `test/03_system/plan_acceptance/` before the fix)

1. **ORA-002 exempted `var` bindings.** `_assignment` only fed `val` bindings to
   the tautology check, so `var x = 8` / `expect(x).to_equal(8)` passed the
   blocker that exists to catch exactly `val x = 8` / `expect(x).to_equal(8)`.
   Two lanes disclosed using it deliberately ("the tool's own heuristic
   explicitly exempts var"). Eight `var x = N` / `expect(x).to_equal(N)` pairs existed across 3 specs (4 + 2 + 2).
2. **A trailing comment defeated the tautology comparison.** `_assertion_parts`
   took everything after `).to_equal(` as the expected text, so
   `expect(x).to_equal(7)  # oracle: doc-recorded` parsed `expected` as
   `7)  # oracle: doc-recorded` — never equal to the binding `7` — while the
   same comment's `# oracle:` marker excused ORA-003. One line earned both
   exemptions. `_is_real_assertion`'s literal-vs-literal check had the same hole.
3. **EVD-001 counted `evidence(` inside `#` comments.** The capture detector had
   no comment exclusion, so `# evidence(assertion): the fixed reference exit
   code above is this scenario's evidence` earned the evidence dimension with
   no capture. Specs with an EVD-001 finding went from 8 to 20 of 35 when it closed; the scorer's own
   `test/01_unit/app/sspec_maintain/scoring_spec.spl` relied on it too.
4. **MNT-009 reported existing paths as stale.** Lifecycle tokens kept sentence
   punctuation (`doc/03_plan/x.md.` / `x.md,`) and bare directories
   (`doc/01_research/`), so every acceptance spec whose docstring ended a
   sentence with the plan path lost 10 maintainability points for a real file.

## Fix

- `_assignment` accepts `val` and `var`; a new `_is_reassignment` marks a
  binding reassigned (`x =`, `x +=`, `x[…] =`, `x.push(…)`) and the tautology
  check skips reassigned names — the loop-flag case the `var` exemption was
  protecting (`var found = false … found = true … expect(found)`) still passes
  (measured 100), the keyword dodge is a blocker (measured 49).
- `_cut_comment` strips a trailing comment outside strings before
  `_assertion_parts` / `_is_real_assertion` parse the expected side. The
  `# oracle:` / `# explained:` ORA-003 markers still read the full line.
- A `#` line counts as a capture only via `@capture` or `.evidence.sdn` (the two
  forms `spipe_docgen` renders); call-form substrings count on code lines only.
- Lifecycle tokens drop trailing `. , ; : )` and bare-directory tokens are skipped.

## Effect on the tree (SCAN surface, seed lane, after the fix)

`clang_board_bringup_x86_64_uefi_spec`, `simpleos_nodejs_ai_cli_migration_spec`,
`simpleos_production_master_plan_completion_status_spec`: **94 → 49** (ORA-002
blocker, the `var` dodge). 22 specs: evidence 100 → 70 (three EVD-001 each,
comment prose no longer counts) — still ≥ 91. `unit_professional_source`
fixture of `scoring_spec.spl` still 100. Every number and the per-rule
calibration fixtures: `scripts/check/sspec-score-seed-lane.shs`.

## Specs

- Reproducing: `test/01_unit/app/sspec_maintain/scorer_loopholes_spec.spl`
- Generalization (adjacent shapes that must NOT fire):
  `test/01_unit/app/sspec_maintain/scorer_loopholes_adjacent_spec.spl`

Both are unexecuted by `bin/simple test` on this host (no full CLI); their
fixture texts were measured through the seed lane on 2026-09-05.
