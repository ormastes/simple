# Detector Standard

Scope: anything that REPORTS defects — `scripts/check/check-*.shs` guards, census
scanners, lint sweeps, coverage-gap lanes. Fixes have a written standard
(red-first reproducer + similar-case tests + sabotage proof); this is the
equivalent for detectors. Harvested from guards that already work, not invented.

A detector that cries wolf is worse than no detector: it burns a session's
triage budget and trains readers to step over a red. Every rule below is
mechanically checkable; unenforceable advice was left out on purpose.

## Checklist (all mandatory before a detector is BLOCKING)

1. **Fatal `--selftest` with must-PASS *and* must-FAIL fixtures.**
   Must-PASS alone proves nothing — a detector that always says PASS passes it.
   Ratios that already ship: 16 must-fail / 7 must-pass / 1 env-isolation
   (`scripts/check/check-tree-size-push.shs:836`); 8 fixtures incl. must-SKIP
   (`scripts/check/check-c-runtime-compiles-push.shs:333`); incident-replay +
   forward-progress + single-removal + empty-range
   (`scripts/check/check-runtime-api-regression-push.shs:375`).
   The selftest runs before EVERY scan and a failure downgrades to ERROR, never
   to a pass (`check-runtime-api-regression-push.shs:389-392`).
2. **Non-vacuity: `n > 0` or ERROR.** Verdict is the last stdout line:
   `PASS — <n> X checked, ...` / `FAIL — ...` / `ERROR — nothing was checked`
   (exit 0/1/2). A run that examined 0 items is ERROR, never a pass
   (`check-c-runtime-compiles-push.shs:390`, `check-tree-size-push.shs:189`).
   See `.claude/rules/vcs.md` for the full convention.
3. **Three-way classification — "can't tell" is never a pass.** PASS / SKIP /
   FAIL, with SKIP counted and printed separately and never folded into the
   compiled count (`check-c-runtime-compiles-push.shs:42-47,168,398`).
   Absence of the tool needed to decide is ERROR, not PASS.
4. **Read the exit code on the line AFTER the command, never through a pipe.**
   `_rc=$?` immediately following (`check-c-runtime-compiles-push.shs:181`).
   A pipeline's `$?` belongs to `tail`/`grep` and has produced false greens here.
5. **Escapes are explicit and RECORDED in the verdict, never silent thresholds.**
   `--expect-files <n>` (`check-tree-size-push.shs:895`), `--expect-removals <n>`
   (`check-runtime-api-regression-push.shs:404`). The escape recentres ONE axis
   for ONE run and prints the accepted number; no flag or env var disables a
   check.
6. **Multiple independent invariants over one clever one.** The tree-size guard
   runs a size band, duplicate-entry, `src/` entry band and path floors — the
   duplicate-entry corruption had a HIGHER file count than healthy, so a
   count-only check was blind to it.
7. **Do not union populations that are legitimately parallel.** Rust and C
   `rt_*` symbol sets are evaluated separately; unioning them was tried and
   masked real Rust-only removals (`check-runtime-api-regression-push.shs:128-129`).
   Record such anti-FP decisions in the script header where they can be reread.
8. **STATED, MEASURED false-positive rate on a NAMED sample — before promotion.**
   No detector goes from advisory to blocking without a header line of the form:
   `# FP-RATE: k/N (<pct>%) on <named sample>, measured <date>, method: <how>`
   `N` must be a reproducible sample (a listed set of hits, or "first N of the
   full hit list in file order"), hand-adjudicated, and `N >= 15` or the whole
   population if smaller. Two detectors in this repo self-reported ~93% FP
   (dangling-import census, 14/15 sampled) AFTER being acted on; that is the
   failure this rule exists to prevent. A detector with an unmeasured FP rate
   stays ADVISORY and must label its output an UPPER BOUND (rule 9).
9. **Label COUNT vs UPPER BOUND.** A number is a defect COUNT only if every
   reported hit was adjudicated a real defect. Otherwise it is an UPPER BOUND
   and must be written that way in the verdict, the doc, and the commit message
   — e.g. "137 paren-less `.length` sites (UPPER BOUND: includes struct fields
   legitimately named `length`)". Never state an upper bound as a count.
10. **Mutation proof.** The selftest must contain at least one fixture that
    deliberately breaks the thing being detected and asserts FAIL with the exact
    expected text (`check-runtime-api-regression-push.shs` incident-replay
    against real commit `6e2f613d302`). A guard that survives its own subject
    being sabotaged is not detecting it.
11. **Wired, not merely written.** A blocking detector must be invoked by
    `scripts/check/pre-push-conflict-tree-guard.shs` (or its lane's runner) and
    that wiring is itself checked by `scripts/check/check-guard-wiring.shs`.
    An unwired guard is advisory by definition, whatever its header claims.

## Promotion gate (advisory -> blocking)

Advisory is the default and is honourable. Promote only when 1-11 all hold, the
FP-RATE header line is present and dated, and the detector is currently GREEN on
`main` (land it advisory first if it is honestly red — precedent:
`check-c-runtime-compiles-push.shs` landed advisory at `04848434af0c`).
