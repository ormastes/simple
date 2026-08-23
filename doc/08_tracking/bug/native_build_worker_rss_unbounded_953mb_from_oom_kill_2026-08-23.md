# native-build worker RSS grows unbounded to within 953 MB of the earlyoom kill

- **Date:** 2026-08-23
- **Status:** OPEN — measured and quantified, not fixed
- **Severity:** memory-safety (an OOM kill here is indistinguishable from a compiler crash)
- **Tree:** `origin/main` @ `61535e69437`
- **Binary:** Rust seed, 60,650,360 B, sha256 `f6521b60b67d38944016b82451ac60c522375410c60dec7178d5c06bd063bde7`
- **Box:** 32 CPU / 125 GiB, load 24–27, MemAvailable 68–72 GiB
- **Full measurement:** `doc/10_metrics/perf/compiler_peak_rss_and_throughput_2026-08-23.md`

## Symptom

`simple native-build` does its work in `simple run
src/app/cli/native_build_worker.spl` child processes. The worker's RSS rises
**monotonically and does not plateau**. Two independent sampled runs (200 ms
interval) peaked at **2726 MB** and **2836 MB** and were *still climbing* when
each run aborted on an unrelated semantic error — so the true peak of a
successful build was never observed and is strictly higher.

Growth rate over the 35–51 s window of run 1: 2089 → 2726 MB, **~40 MB/s.**

## Why it matters

earlyoom on this host kills `simple` (designated victim) at ~3.7 GiB ≈ 3789 MB.

| quantity | value |
|---|---|
| highest observed worker RSS | 2836 MB |
| headroom to kill | **953 MB — 25 % of budget** |
| growth rate | ~40 MB/s |
| time-to-kill at that rate | **~24 s** |

A build ~24 s longer than the one measured is SIGKILLed, surfacing as
`rc=137`/`143`. That reads as a compiler crash and is not one. Prior sweeps
reported "0 SIGSEGV/SIGTERM deaths" **with peak RSS unmeasured** — that was
zero-by-absence, and this record closes it with numbers.

## Mechanism (partly identified)

The worker interprets `native_build_worker.spl`, whose import closure is the
whole compiler, so it pays two costs stacked:

1. **AST retention.** `IMPORTED_MODULE_AST`
   (`src/compiler_rust/compiler/src/hir/lower/import_loader.rs:33`) holds an
   `Arc<Module>` per imported path for the life of the process. Its only clear
   site is the global `clear_module_cache` (`module_cache.rs:191`) — **never at
   end-of-lowering.** Measured independently on the `compile` path: RSS climbs
   to 1571 MB in 20 s and then sits **perfectly flat for the remaining 32 s
   (62 % of the run), releasing nothing.**
2. **Interpreter state on top** — module globals/HIR/MIR accumulation, which is
   what makes the worker curve *keep climbing* where the `compile` curve
   plateaus. This half is **not yet attributed to a specific structure.**

Note the memo itself is a landed, correct fix for a real 112x *re-parse* defect
and is pinned by parse COUNT
(`imported_module_ast_memo_tests::repeated_import_of_the_same_module_parses_it_exactly_once`).
The defect here is its **retention lifetime**, not its existence. Do not remove
the memo — that would reinstate the re-parse blowup.

## Open questions for whoever fixes this

1. Is `IMPORTED_MODULE_AST` consulted **after** HIR lowering completes? If not,
   clearing it there frees ~1.5 GiB before MIR/codegen, semantics-preserving.
   Not attempted here: the payoff phase (MIR/codegen) could not be observed,
   because every closure tried aborts in the semantic phase, and a fix justified
   by an unobserved phase cannot be shown to discriminate.
2. What accounts for the worker's *continued* climb past the AST plateau?
   Needs allocation attribution (`SIMPLE_MEM_TRACE=1`, `SIMPLE_BIG_ALLOC_MB`),
   which did not produce an attribution in this session.
3. Should the worker cap concurrency by measured per-worker RSS rather than CPU
   count? At 2.8 GiB/worker, two concurrent workers exceed 5.6 GiB.

## Blocker encountered while measuring (separate defect)

`origin/main` @ `61535e69437` cannot compile its own driver with this seed:

- `src/app/cli/bootstrap_main.spl` → `semantic: Undefined("undefined identifier: panic")`
- `src/app/info/main.spl` → `semantic: Undefined("undefined identifier: fetch_index_entry")`
- `native-build src/app/any_audit/main.spl` → `semantic: unknown extern function: rt_heap_ref_wellformed`

These are **already-known** defects owned by other lanes, recorded here only
because they bounded what could be measured (no full closure compile reached
MIR/codegen). The `rt_heap_ref_wellformed` seed gap is
`doc/08_tracking/bug/seed_rejects_rt_heap_ref_wellformed_blocks_redeploy_2026-08-23.md`;
the `undefined identifier` mass class is the seed resolver not registering
`use ... as ALIAS` renamed imports, censused in
`doc/09_report/compile_census_2026-08-23.md` (3,640 files = 23.9 % of `src/`).
Nothing new is claimed about them here.

## Reproduce

```sh
# Samples the WORKER DIRECTLY (it is the parent here, so $p is correct).
# For `native-build`, do NOT copy this: the parent stays at ~54 MB and the
# memory is in children — match /proc/*/exe against your binary path instead.
./bin/simple run src/app/cli/native_build_worker.spl src/app/any_audit/main.spl -o /tmp/w.bin &
p=$!; while kill -0 $p 2>/dev/null; do awk '/VmRSS/{print $2}' /proc/$p/status; sleep 0.2; done
```

Record load average and MemAvailable alongside — this box runs at load 24–33.
