# An execution lane can report a clean result without ever having run
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-01
**Found by:** the COW-scoping agent; **verified by the parent.**
**Status:** CLOSED 2026-11-11 — FIXED on release; verified by lane ne8 (seed 46fe8f6b6def). General testing hazard — not specific to COW.

## Measured

```
$ SIMPLE_EXECUTION_MODE=llvm bin/simple run test/cow_probe.spl
[engine-demotion] reason=jit-compile-error detail=LLVM JIT not available: compile with feature 'llvm'
ALIASED   7 struct by-value fn arg, nested array      <- 1 of 16, i.e. the INTERPRETER's result
```

```
$ SIMPLE_EXECUTION_MODE=cranelift bin/simple run test/cow_probe.spl
(0 demotion lines)
11 ALIASED                                            <- genuinely executed
```

The `llvm` lane silently fell back to the interpreter and produced the
interpreter's answer under an LLVM label. **Its clean result is not evidence
about LLVM.** Had the demotion line scrolled past — or been filtered by a grep
looking only for verdicts — that run would have been recorded as "LLVM lane:
correct."

## Why this matters beyond one flag

This is the same class as the other silent-pass defects found today, and it is
the most dangerous variant because it corrupts *measurement* rather than
computation:

- [[simple_run_exit_code_garbage_for_unit_main_2026-09-01]] — exit codes are
  meaningless, so rc cannot gate anything.
- [[transport_profile_sdn_path_cwd_dependent_2026-09-01]] — a missing config
  becomes ~150 plausible assertion failures rather than "not found".
- A watchdog kill at 10s prints **no verdict at all**, which reads as a silent
  pass unless the reader requires the verdict token explicitly.
- And now: a lane can be selected, appear to run, and report another lane's
  result.

In a matrix comparing execution lanes, this defect makes the compared lanes
**silently identical**. A whole column of a comparison table can be fiction.

## Required

1. A lane that cannot honour its selection must **fail**, not demote — or, if
   demotion is a deliberate resilience feature, it must be impossible to
   *silently* accept its output as that lane's result.
2. Any lane-comparison harness must **assert the lane actually ran** before
   recording a result: require the absence of `[engine-demotion]`, or a positive
   `[engine-receipt]` naming the engine that executed.
3. Treat `SIMPLE_EXECUTION_MODE` as load-bearing and document it. It is currently
   undocumented, yet it selects between engines that **disagree on language
   semantics** — see
   [[struct_nested_array_assign_aliases_not_cow_2026-09-01]] (cranelift 11/16
   shapes alias, interpreter 1/16).

## Reporting rule adopted for this session

An execution-lane result is admissible only when the run emitted **zero**
`[engine-demotion]` lines. Every lane row must state whether it genuinely
executed. The LLVM/native column of the COW table is therefore recorded as
**UNTESTED**, not as clean.

## Caveat

Measured on the Rust bootstrap seed. `SIMPLE_EXECUTION_MODE` appears as a string
in the deployed binary but in no `.rs`/`.spl` source under `src/` — the deployed
binary is not built from this worktree, so the demotion logic cannot be cited
here.


---

## 2026-11-11 addendum — lane ne8 (P3 traverse, batch ne8)

**Verdict: FIXED on release** (the "impossible to silently accept" branch of Required #1).

- **Fixing change:** non-forgeable engine receipt `src/compiler_rust/common/src/engine_receipt.rs`
  (fix `498eb1fc078`, guard + fixture pair `cc173c44cb4`, 2026-08-23; recorded in
  `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` §20/§27). The engine
  field is stamped from INSIDE the engine that actually executes; no flag can set it; a demotion
  is announced on stderr unconditionally (`[engine-demotion]`, no suppressing knob) whenever a
  compiled lane was requested — and an UNSET `SIMPLE_EXECUTION_MODE` deliberately counts as
  requesting the compiled lane, because the seed's default lane already is the JIT.
- **This doc's exact scenario re-run (seed-smoke, seed 46fe8f6b6def):**
  `SIMPLE_EXECUTION_MODE=llvm SIMPLE_ENGINE_RECEIPT=1 simple run <probe>` now prints
  `[engine-demotion] reason=jit-compile-error ...` on stderr AND a receipt naming what really
  ran: `[engine-receipt] engine=interpreter requested=llvm demoted=yes reason=...`. An
  `interpret` request yields `engine=interpreter requested=interpret demoted=no`. The
  interpreter's answer can no longer be laundered into an LLVM result.
- **Fail-closed guard:** `scripts/check/check-engine-receipt-discriminates.shs` — selftest 8/8;
  full run on this seed: **PASS — 10 assertion(s) checked, receipt discriminates
  (clean=cranelift-jit, demoted=interpreter)**. Its discriminating fixture pair
  (`test/fixtures/engine_receipt/{jit_clean,demote_graphics_text}.spl`) had been deleted in the
  2026-11-07 snapshot commit `4edef8fab8e1`, leaving the guard at ERROR "nothing was checked";
  lane ne8 restored both fixtures byte-identical from `cc173c44cb4` (commit
  `test(seed): engine-receipt guard + discriminating fixture pair`) and the guard now runs green.
  This restoration ships in the same commit as this addendum.
- **Required #3 (documentation):** `SIMPLE_EXECUTION_MODE` and the receipt contract are
  documented in `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`; the
  receipt line format `[engine-receipt] engine=<E> requested=<R> demoted=<yes|no> reason=<R|->
  file=<P>` is pinned by the guard's selftest fixtures.
