# Cert Phase-4 stress/robustness findings

Originally: confirmed defects discovered while building
`scripts/check/cert/stress-suite.shs`, reproduced on the deployed clean
compiler `bin/release/x86_64-unknown-linux-gnu/simple` (default compiled
backend unless noted). Each was re-run live (non-gating) by the suite's
FINDINGS section so the defect would be demonstrated, not merely asserted.

**Status as of 2026-07-17 (STRESS lane re-verification): all three original
findings (f01/f02/f03) are resolved for the CORE gate's own invocation.**
Full root-cause writeups and verification commands live under
`doc/08_tracking/bug/stress_f0{1,2,3}_*_2026-07-17.md`. Summary:

## f01 — deep-nesting stack overflow — FIXED

Already fixed by an earlier, unrelated commit
(`4274c4f3f20b fix(seed-parser): bound expr/type recursion to prevent
stage-4 SIGABRT`) before this lane started. `f01_deep_nest_stackoverflow.spl`
(5000 balanced parens) now gets a clean, located parse error
("expression nesting exceeded 512 levels without progress", `rc=1`) instead
of SIGABRT. Kept here as a live, non-gating demonstration of that graceful
behavior at the original crash-reproducing depth. The general regression
guard for this class (over-cap-but-otherwise-valid nesting must reject
cleanly) is now also asserted directly in the CORE gate as
`deep_paren_over_cap`. See
`doc/08_tracking/bug/stress_f01_deep_nest_parser_recursion_2026-07-17.md` —
including the side effect this cap has on legitimately-deep (>512) valid
nesting, which the CORE gate now accounts for explicitly rather than hiding.

## f02 — large integer literal codegen — FIXED

Root-fixed 2026-07-17 (STRESS lane): `print(9223372036854775807)` (i64::MAX)
now prints correctly on the compiled/JIT backend (was `-1`). Root cause and
fix: `doc/08_tracking/bug/stress_f02_i64_boxing_truncation_2026-07-17.md`.
Promoted from a `findings/*.spl` repro into a pinned CORE `valid_case`
(`bigint_i64_max`, `test/cert/stress/gen/bigint_i64_max.spl`) — no longer
lives under `findings/`.

## f03 — many function calls in one expression — FIXED for the gate's own invocation; narrower residual open

The compiled/JIT default path (what this suite's `_run` helper actually
invokes) now computes the correct sum (`44850`); the original
"garbage/divergent on both backends" symptom traced to something already
fixed by an earlier, unrelated commit before this lane started. Promoted to
a pinned CORE `valid_case` (`manycall_sum_300`,
`test/cert/stress/gen/manycall_sum_300.spl`) — no longer lives under
`findings/`.

A narrower, DIFFERENT residual bug was found during re-verification: the
tree-walking interpreter (`SIMPLE_EXECUTION_MODE=interpret`, not what this
gate exercises by default) resolves a user-defined function literally named
after a primitive-cast builtin (e.g. `fn f64() -> int: ...`) to the BUILTIN
cast instead of the user's function, by explicit interpreter dispatch-order
design ("so builtins can't be shadowed"). This is left OPEN — it's a
deliberate cross-cutting policy, not a narrow codegen bug, and out of scope
for this lane. Full detail, isolated repro, and suggested fix shapes:
`doc/08_tracking/bug/stress_f03_manycall_sum_2026-07-17.md`.
