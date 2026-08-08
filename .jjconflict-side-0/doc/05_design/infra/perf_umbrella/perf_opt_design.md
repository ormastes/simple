# Performance Optimization Umbrella — Design

Connective-tissue design for the perf umbrella: the **benchmark harness**, the
**API/arch no-break guard**, and the **dynSMF idle-compile + content-hash cache** build.
Optimizations themselves are per-domain and tracked as sub-goals; this doc designs the
machinery that makes them safe, measurable, and arch-extensible. No inheritance — composition,
traits, and tag descriptors only.

<!-- sdn-diagram:id=perf-umbrella-flow
flow {
  baseline[Benchmark sspec harness] -> docs[doc/09_report + doc/10_metrics]
  baseline -> guard[API/arch snapshot]
  guard -> diff[per-phase ABI diff]
  optimize[per-domain opt .spl] -> diff
  optimize -> rerun[re-run harness]
  rerun -> docs
  diff -> gate{no API/arch break?}
  gate -> |yes| land[land sub-goal]
  gate -> |no| block[block + escalate]
  dynsmf[dynSMF dispatch+hash] -> cachespec[smf_cache_reuse_spec]
}
-->

## Modules

| File (new=+, mod=~) | Purpose |
|---|---|
| `+ src/app/test/bench/bench_harness.spl` | Reusable benchmark runner: times a closure N iters, emits warm/cold/throughput/RSS rows; arch+mode tagged |
| `+ src/app/test/bench/bench_report.spl` | Renders results → markdown (`doc/09_report/perf/`) + table (`doc/10_metrics/perf/`) |
| `+ test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | AC-4: interpreter vs smf vs native rows, separated |
| `+ test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` | AC-5: ram-only / persistent / wal rows, separated |
| `+ test/05_perf/web/web_server_bench_spec.spl` | Web cold-start/req-s/latency/RSS |
| `+ test/05_perf/os/os_fs_sched_bench_spec.spl` | OS fs/exec/sched over QEMU x86_64 |
| `+ src/app/cli/api_surface_snapshot.spl` | AC-8: emit public-symbol SDN via `symbol_analyzer.spl`+`metadata_symbol_surface.spl` |
| `+ scripts/check/check-api-arch-guard.shs` | Diff current snapshot vs `doc/08_tracking/api_surface/baseline.sdn`; fail on public delta |
| `~ src/app/startup/dynsmf_autoload.spl` | AC-7: dispatch queued background compiles (`process_spawn_async`) |
| `~ src/os/smf/dynsmf_session.spl` | AC-7: add source content-hash guard (replace magic-only check at ~:163) |
| `+ test/02_integration/app/simple/smf_cache_reuse_spec.spl` | AC-7: reuse-on-unchanged + miss-on-changed |

## Key interface (bench harness — no inheritance, tag descriptor + closure)
**Two measurement planes** (advisor correction): in-process closure timing can only measure
**warm micro-throughput**. Cold-start, peak RSS, and binary size are process-launch costs and are
delegated to the existing process-level harness `scripts/check/check-cross-language-perf.shs`
(which already measures size + cold startup + warm fib35 + parallel spawn + RSS across
Simple/Bun/Python/Go/Erlang/Java/C). `bench_harness.spl` does NOT reimplement that; it wraps it
for the `process` plane and adds the `warm` plane.

```simple
struct BenchCase:
    name: text
    arch_tags: [text]      # e.g. ["x86_64"]; arm/riscv added later, same spec via tag
    mode: text             # lang: "script"|"smf"|"native"   db: "ram"|"persistent"|"wal"
    plane: text            # "warm" (in-process closure) | "process" (cold/RSS/size via cross-lang harness)
    iters: i64

fn bench_run_warm(case: BenchCase, body: fn() -> ()) -> BenchResult    # warm throughput, in-process
fn bench_run_process(case: BenchCase, argv: [text]) -> BenchResult     # cold/RSS/size, delegates to harness
fn bench_emit(results: [BenchResult], report_path: text, table_path: text) -> ()
```
AC-4 (script vs compiler) is inherently a `process`-plane comparison (interpreter process vs
native binary); AC-5 (db ram vs persistent) is mostly `warm`-plane with a `process` cold-start row.

## Guard contract (AC-8)
`check-api-arch-guard.shs` is run after every sub-goal: snapshot public symbols → diff vs
baseline → any added/removed/changed public symbol or accessor-forwarding signature = RED.
Pre-existing broken specs (rate_limit/request_validation/security_headers) are listed in a
quarantine file so they never count as a perf-introduced regression.

## dynSMF cache (AC-7)
`simple run` user-script path already content-hashes (keep as-is). Build only the dynSMF
precompiled lane: (1) after autoload, spawn the queued `bin/simple compile` jobs; (2) store a
source SHA sidecar next to the `.smf`; (3) on load, compare SHA before accepting `artifact_ready`.
Invalidation spec proves a changed source re-queues instead of loading the stale artifact.
