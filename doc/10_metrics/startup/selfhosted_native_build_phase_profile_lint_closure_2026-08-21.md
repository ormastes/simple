# Per-phase profile: self-hosted `native-build` of the lint entry closure

- **Date:** 2026-08-21
- **Command:**
  `SIMPLE_CACHE_SCOPE=p36f SIMPLE_HIR_PHASE_PROFILE=1 <seed> native-build --source src/app --entry-closure --entry src/app/cli/lint_entry.spl -o /mnt/data/seedperf/lint_native --threads 2`
- **Closure:** 192 modules
- **Host caveat:** shared box, load average 28-33 with ~20 concurrent `simple`
  processes throughout. Treat every number as an ENVELOPE, not a floor — an
  idle box is faster. Recorded anyway because no per-phase numbers for steps
  2+ existed at all before this run.

## Why this is the first such measurement

Until the fix in `async_desugar_binary_payload_order_swapped_2026-08-21.md`,
every self-hosted `native-build` on a compiler-sized closure died at the END of
step 1/6 with `undefined field: ... 'kind' on enum BinOp`. No run had ever
entered step 2, so steps 2-6 had never been timed on a real closure.

## Phase table (steps 0-2; run still in progress past this point)

| phase | step | n | total | mean/module | max |
|---|---|---|---|---|---|
| source_closure | 0/6 | 12 | 9.0s | 0.75s | 2.5s |
| load_sources | 0/6 | 3 | 25.9s | 8.64s | 10.1s |
| export_origins | 0/6 | 1 | 9.3s | 9.29s | 9.3s |
| surface_build | 1/6 | 192 | 2.7s | 0.01s | 0.2s |
| surface_alias | 1/6 | 344 | 1.2s | 0.00s | 0.0s |
| surface_freeze | 1/6 | 2 | 3.0s | 1.49s | 3.0s |
| **parse** | 1/6 | 775 | **1649.9s** | 2.13s | 61.4s |
| **hir** | 2/6 | 60* | 688.5s | **11.5s** | **130.9s** |

`*` hir was at module 42/192 when this table was cut; the row is a partial
sample, not a phase total. Parse wall-clock to 192/192 was 672s across 2
shards (1650s of summed per-module dt).

## Modules over the 60 s/module flag threshold

| phase | module | dt |
|---|---|---|
| parse | `src/compiler/frontend/core/parser_stmts.spl` | 61.4s |
| hir | `compiler.10.frontend.core.tokens` | **130.9s** |

`compiler.10.frontend.core.tokens` at 130.9s is 11x the hir mean and is the
clearest perf outlier found so far. It is a large token-enum module, which
suggests the cost is in enum/variant lowering rather than in function bodies —
but that is a hypothesis, not a measurement, and locating the superlinear term
needs a profiler pass that this host blocks (`ptrace_scope=1`,
`perf_event_paranoid=4`, same limitation recorded in
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`).

## Open

- Steps 3-6 (MIR lowering, mono, codegen, link) still unmeasured — the run had
  not reached them. This document should be extended, not replaced, when it does.
