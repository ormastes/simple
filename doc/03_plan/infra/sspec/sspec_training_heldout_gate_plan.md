# SSpec Training Held-Out Gate — Plan

**Date:** 2026-09-05 · **Design:** `doc/05_design/infra/sspec/sspec_training_heldout_gate_design.md` · **State:** `.spipe/sspec_training_heldout_gate/state.md`

## Steps

| # | step | owner | done when |
|---|---|---|---|
| 1 | Derive the 14 held-out / 7 same-case lists from `modern_sspec/skill.md` + git history of checklist commit `bf9cd7b` (SPipe repo) | W1 | lists + derivation method recorded in `splits.sdn` header comment |
| 2 | Write `.spipe/training/splits.sdn` | W1 | AC-1 |
| 3 | Add `--split` + two leak gates + 3 selftest fixtures to `sspec-train.shs` | W1 | `--selftest` PASS; AC-2..4 |
| 4 | Run `--split private_test` and `--split train`; record verbatim verdicts in `modern_sspec/skill.md` | W1 | AC-5 |
| 5 | Review diff, re-run selftest + both splits, commit lane | Fable | commit on `work/debug-perf-dump-skills-2026-09-05` |
| 6 | Next training iteration uses `--split private_test` as the only reportable number | anyone | checklist edits cite `train` findings only |

## Known outcomes to expect (not failures)
- Gate A ERRORs the moment anyone edits the checklist. That is the point: the next checklist edit must be followed by a re-freeze (`checklist_digest` updated) AND a *new* held-out set — never by moving a spec to `train`, and never by re-using the old 14 as held-out against a checklist that has since been tuned.
- If `--split private_test` scores below 14/14 ≥90, that is the honest number and replaces "14/14" in the skill doc.

## Correction recorded (2026-09-05)
The first implementation gated on "held-out spec modified after cutoff" (`git log %aI`). It ERRORed on all
14 — correctly, given the rule, and the rule was wrong: the worker edits the held-out spec by design.
Replaced with checklist-digest equality. Kept here so the mistake is not re-made.

## Later (foundry Waves 2–5, engine side — NOT this repo)
`SolverRunV1`, deterministic + model graders, attribution, promotion/GC. Trigger: `Spipe/src/training` lands and reads `splits.sdn`.
