# Bug: JIT wraps large i64 boundary constants (p60/p62/i64::MAX) to negative/zero

**Found**: 2026-08-09, via `scripts/check/check-engine-differential.shs`
(newly wired into pre-push this session, `DIFF_LANES=interpret,jit` fast
config) as a NEW unbaselined divergence: `i64_boundary_values`.

## Symptom

The interpreter and JIT engines disagree on large `i64` boundary constants
(`p60`, `p62`, `i64::MAX`-class values): the JIT wraps them to negative
values or zero, while the interpreter reports the correct value.

## Impact

Any code relying on large `i64` boundary constants under the JIT engine
(the default execution engine for `bin/simple run`) gets silently wrong
values. This is a correctness defect, not a performance issue.

## Next step

Root-cause in the JIT's constant-lowering path for `i64` boundary values —
likely a truncation/sign-extension bug in how large literal constants are
encoded for the JIT backend. Reproduce via
`scripts/check/check-engine-differential.shs DIFF_LANES=interpret,jit` and
inspect its fixture corpus for the exact `i64_boundary_values` case. Until
fixed, `check-engine-differential.shs` is wired in RED on purpose in
`scripts/check/pre-push-conflict-tree-guard.shs` (same convention as
`lint_binary_staleness_guard`/`native_object_cache_granularity_guard`) so
this stays visible rather than being silently baselined away.
