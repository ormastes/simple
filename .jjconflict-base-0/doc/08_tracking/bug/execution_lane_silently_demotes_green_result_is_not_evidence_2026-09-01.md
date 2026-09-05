# An execution lane can report a clean result without ever having run

**Date:** 2026-09-01
**Found by:** the COW-scoping agent; **verified by the parent.**
**Status:** OPEN. General testing hazard — not specific to COW.

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
