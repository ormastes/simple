# BUG: native path — untyped text `==` never matches + fused boolean conditions evaluate wrong

**Status (2026-07-15):** source implemented; historical native/oracle
regression evidence is recorded in `e4471d60acb6`.

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
