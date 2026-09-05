# Feature Specification – Check-Script Non-Vacuity Ratchet

**Requirements:** (proposed — research at
`doc/01_research/compiler/silent_failure_taxonomy_2026-09-01.md`)
**Plan:** (proposed — no plan doc yet)
**Design:** (proposed)
**Status:** Draft

## Feature Description

A check script that can print PASS after examining zero items is caught the day
it lands, by a meta-guard that enforces the repo's own non-vacuity convention
(`PASS — <n> item(s) checked`, `n == 0` ⇒ ERROR) over `scripts/check/` itself —
instead of the convention living only in `.claude/rules/vcs.md` prose and in
whichever guards happened to adopt it.

## Problem this addresses

Measured 2026-09-01 (methodology in the research doc):

- 795 scripts in `scripts/check/*.shs`; **503 print PASS; only 285 carry the
  non-vacuity convention** (`nothing was checked` / `EV_CHECKED`). 219 do not.
- **29 scripts confirmedly iterate a DISCOVERED list (find/`git ls-files`/glob),
  print PASS, and contain no zero-count guard and no ERROR text at all** — an
  empty discovery falls straight through to PASS. Full list in the research doc
  §2.1.
- The class has already bitten: `check-no-unresolved-runtime-symbols.shs`
  measured GREEN on Linux with no artifact to inspect while Windows had 68
  unresolved; the test runner reported green on an explicitly empty selection
  (`test_runner_explicit_empty_selection_false_green_2026-07-24.md`); six specs
  reported `executed=0` after a parse crash with nothing flagging it.
- The convention itself has no ratchet — the one defect class it exists to
  catch, recurring one level up.

## Scenarios

### Scenario: A new PASS-capable check script lands without a non-vacuity assertion

**Given** a push adds `scripts/check/check-foo.shs` that prints `PASS` and has no `n == 0` ⇒ ERROR handling
**When** the developer pushes
**Then** the meta-guard FAILs, naming the script and the missing convention, with a pointer to the verdict-line idiom in `.claude/rules/vcs.md`

### Scenario: Pre-existing debt does not block unrelated work

**Given** the 219 existing convention-less scripts are frozen in `scripts/check/non_vacuity_baseline.txt`
**When** a developer pushes a change touching none of them
**Then** the meta-guard PASSes, reporting the baseline count

### Scenario: A baselined script is repaired

**Given** `check-window-winit-leak.shs` (baselined) gains a non-vacuity assertion
**When** the developer pushes without regenerating the baseline
**Then** the meta-guard FAILs as STALE BASELINE, forcing the baseline row's removal — a baseline that no longer describes the tree must not keep ratcheting silently

### Scenario: The meta-guard cannot itself pass vacuously

**Given** the meta-guard's scan finds zero check scripts (wrong cwd, archive worktree)
**When** it runs
**Then** it prints `ERROR — nothing was checked` and exits 2, never PASS

### Scenario: A builder script is not misclassified

**Given** `scripts/check/build-mlkem-simd-c-lane.shs` prints PASS as build progress but emits no verdict over discovered items
**When** the meta-guard classifies it
**Then** it is reported in a separate `non-verdict` category, neither required to carry the convention nor counted as debt

## Acceptance Criteria

- [ ] Meta-guard `scripts/check/check-non-vacuity-convention.shs` exists, follows the standard verdict convention (`PASS — <n> script(s) checked, 0 new` / `FAIL — ... naming each offender` exit 1 / `ERROR — nothing was checked` exit 2)
- [ ] Classification distinguishes: convention-carrying / PASS-capable-without-convention / non-verdict (builders); the classifier's rules are documented in the script header
- [ ] Baseline file freezes the current convention-less population; a NEW offender fails; a repaired-but-still-baselined script fails as stale (same two-direction rule as `check-unbacked-extern-ratchet.shs`)
- [ ] `--generate-baseline` exists for reviewed updates only
- [ ] `--selftest` runs before every scan and is fatal, with at least 4 fixtures: clean PASS; new offender FAIL naming it; stale baseline FAIL; empty scan ERROR
- [ ] The 29 confirmed vacuous-capable scripts (research doc §2.1) are triaged: each either gains a non-vacuity assertion or gets a one-line header comment stating why an empty scan is legitimately PASS — zero left untriaged
- [ ] Wired as a push-tier row in `config/check/must_check_gates.sdn` with measured cost recorded (expected <5s: it is a textual scan)

## Out of Scope

- **Fixing the 219 baselined scripts.** The ratchet freezes debt; only the 29
  confirmed-vacuous get hand triage.
- **Enforcing predicate ENTAILMENT** (P2 in the taxonomy — a guard that
  examined n>0 items with a non-discriminating predicate). No textual scan can
  judge whether evidence entails a verdict; that stays per-guard engineering.
- **Semantic proof of vacuity.** The classifier is textual and errs toward the
  `non-verdict` category on ambiguity; a false `non-verdict` is acceptable, a
  false `convention-carrying` is not.
- **Blocking on scripts outside `scripts/check/`.** Bootstrap-stage scripts and
  `scripts/build/` have their own chicken-and-egg constraints (a stage guard
  may legitimately find no artifact before the stage exists); do not extend
  scope there without the bootstrap owners.

## Notes

Highest value/cost of the taxonomy's proposals: the idiom, baseline mechanics,
selftest shape, and manifest wiring all already exist
(`check-unbacked-extern-ratchet.shs` is the model); this is one script plus one
baseline file, and it converts the repo's strongest documented convention into
an enforced one.
