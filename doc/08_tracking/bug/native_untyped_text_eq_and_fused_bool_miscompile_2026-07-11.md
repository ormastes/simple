# BUG: native path — untyped text `==` never matches + fused boolean conditions evaluate wrong

**Status (2026-07-15):** RESOLVED — verified fixed at origin tip 8932fcb3a148.

## Resolution

Erased text equality now uses the shared runtime content comparison instead of
comparing handles. The frontend preserves the actual unary operator, and LLVM
widens logical `not` through the existing comparison helper. No fresh
execution was performed during the 2026-07-15 source audit.

## Symptoms (in the natively-compiled bootstrap_main binary)

1. `text == text` comparisons never match on untyped receivers (argv-derived
   values): every equality guard is dead.
2. Fused boolean conditions (`not a.starts_with(..) and a.ends_with(..)`)
   evaluate wrong even when their operands, bound to individual `val`s first,
   are each provably correct (traced: `dash=0 spl=1` yet the combined
   condition's counter stayed 0).

## Analysis

Both are in the untyped-receiver lowering family (#137/#138): with
`MethodResolution.Unresolved`, text `==` presumably lowers to raw i64 compare
of tagged string handles (pointer identity, not content — needs an
rt_string_eq interception like len/starts_with/ends_with/substring), and the
boolean fusion suggests `not`/`and` mis-lowering over i1-vs-i64 or the eager
`and` path combining wrongly.

## Repro

Extend `src/app/cli/bootstrap_main.spl` with a text `==` guard over argv, build
on the normal native path (env -u SIMPLE_BOOTSTRAP + forced worker +
SIMPLE_RUNTIME_PATH), run with matching argv — guard never fires.

## Verification (2026-07-16)

Verified fixed at origin tip 8932fcb3a148: `probe06_untyped_text_eq_a.spl` (`fn check(a: text) -> i64` computing `a == "spl"`, `a.starts_with("d")`, `a.ends_with("l")`, and fused `not starts_d and ends_l`; called with `"spl"` and `"dashl"`). Oracle: `bin/simple run` → `11` then `0`. Native: `native-build --entry --clean` exit 0, binary built, run → `110` (= both values concatenated, matches oracle). Text equality now uses shared runtime content comparison and boolean fusion evaluates correctly.
