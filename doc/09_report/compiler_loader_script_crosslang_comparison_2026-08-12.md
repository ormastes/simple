# Compiler, loader, script, and cross-language comparison

Status: diagnostic comparison only. No final Stage 4 result is claimed. Every
number below comes from a retained artifact and is marked with its exact path.

## Evidence classes

| Class | Treatment |
|---|---|
| Retained diagnostic table | useful for relative shape; not release-admitted unless identity, provenance, actual-mode, checksum, and RSS gates are satisfied |
| Design target | engineering budget or proposed technique; not a measurement |
| Blocked/missing | no number is available and no performance conclusion is drawn |

The current harness requires canonical self-hosted provenance and rejects Rust
bootstrap fallback. Source: `/mnt/data/bs2/simple-perf-final-9c/scripts/check/check-cross-language-perf.shs`.

## Simple mode comparison

The retained 20-run profile reports these cold hello averages and fib(35) warm
rows. They are diagnostic because that report predates the current provenance
and actual-mode receipt admission rules.

| Mode | Cold hello (ms) | fib(35) (ms) | Interpretation |
|---|---:|---:|---|
| Simple interpreter | 38.175 | 106.306 | source/tree-walk row; outer-process timing for warm row |
| Simple SMF loader | 33.412 | 136.325 | bytecode/loader row; outer-process timing for warm row |
| Simple native | 4.087 | 76.738 | AOT row; not a compiler-time measurement |

Exact retained artifact: `/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

The same report lists artifact footprints of 38.0 B/175.0 B for source hello/fib,
3.0 KB/3.7 KB for SMF hello/fib, and 451.4 KB/452.6 KB for native hello/fib;
these are source/artifact-size categories, not total deployed process size.
Exact retained artifact: `/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

## C, Rust, Go, Python, and Bun

The retained 20-run report provides numeric C, Go, Python, and Bun rows, but no
Rust row. Rust is present in the newer harness source as a required
comparison producer, but a source contract is not a measured result. Exact
harness path: `/mnt/data/bs2/simple-perf-final-9c/scripts/check/check-cross-language-perf.shs`.

| Runtime | Cold hello (ms) | fib(35) warm (ms) | Status |
|---|---:|---:|---|
| C (gcc -O2) | 4.028 | 17.707 | diagnostic retained row |
| Go | 61.853 | 57.680 | diagnostic retained row |
| Python | 27.080 | fail | failed workload, not a speed result |
| Bun | 105.111 | 93.033 | diagnostic retained row |
| Rust | — | — | no retained numeric row in this report |

Exact retained artifact for all numeric cells in this table:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

The report uses 20 runs and 10 in-process warmups; those settings are evidence
metadata, not transferable claims about another machine. Exact retained path:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

## Concurrency shape, not a single aggregate

The retained profile keeps OS threads, cooperative green work, and multicore
green work separate. For 100 OS-thread workers, it reports C at 11.778 ms, Go at
9.816 ms, Simple native at 98.080 ms, and Simple SMF at 137.602 ms. For 1,000
tiny-worker fanout, it reports C at 72.757 ms, Go at 7.556 ms, Simple native at
87.933 ms, and Simple multicore-green native at 18.233 ms. These rows are
diagnostic and must not be used to claim Go-like semantics for cooperative
queues or an unverified pool.

Exact retained artifact: `/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

The report records 100 CPU workers, Go `GOMAXPROCS=100`, 100 OS-thread workers,
1,000 fanout workers, and a 20-second per-run timeout. Exact retained artifact:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/cross_language_perf_2026-06-13.md`.

## Compiler speed and loader speed

No retained numeric compiler-time row is available in the reviewed evidence.
The newer harness contains a `retained_compile_measure` producer that measures
native compilation wall time and RSS, but its source is not itself a retained
result. Therefore compiler speed is **open**, not zero and not inferred from
native runtime speed. Exact source path:
`/mnt/data/bs2/simple-perf-final-9c/scripts/check/check-cross-language-perf.shs`.

The loader investigation documents mmap-backed SMF caching, symbol resolution,
and load-time generic instantiation as architecture. It does not establish a
cross-language loader timing row. Exact path:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/2026/02/loader_architecture_investigation_2026-02-04.md`.

For unchanged user scripts, the retained cache research says source and
dependency interface hashes validate cached SMF; the dynSMF precompiled lane
remained partial because magic-byte readiness did not establish source freshness.
Exact path:
`/mnt/data/bs2/packed-memory-32ead/.spipe/perf-opt-lang-web-db-os/research/02_smf_idle_cache.md`.

## Memory and bug interpretation

The retained shared-text baseline measured 200,292 KiB parser RSS and 449,272
KiB for 10,000 distinct short strings. It set ceilings of 220,321 KiB and
494,199 KiB; later bounded parser evidence recorded 33 ms, 75 ms, and 205,192
KiB. These values belong to separate baseline/WIP artifacts and must not be
combined into one regression claim.

Exact paths:

- `/mnt/data/bs2/packed-memory-32ead/doc/09_report/perf/interpreter_shared_text_rss_baseline_2026-07-13.md`
- `/mnt/data/bs2/packed-memory-32ead/doc/09_report/perf/interpreter_shared_text_compile_wip_2026-07-13.md`

Memory rows are inadmissible when the fixture does not prove actual output
length/content or when the executable is a seed diagnostic. The retained WIP
also records unrelated full-suite failures and a pending larger bootstrap
acceptance; it is not evidence of a final compiler memory pass. Exact path:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/perf/interpreter_shared_text_compile_wip_2026-07-13.md`.

## Missing techniques and next evidence

The performance architecture proposes semantic incremental CAS identity,
demand-driven queries, register/adaptive bytecode, low-latency native code,
precomputed aspect plans, and a persistent compiler service. They are not
measured in this comparison. Exact path:
`/mnt/data/bs2/packed-memory-32ead/doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`.

The next admissible run must produce, for each Simple source/SMF/native row,
the exact executable and compiler hashes, provenance receipt, requested and
actual mode, fallback flag, checksum, raw samples, p50/p95, max RSS, and an
explicit rejection reason for anything unavailable. The receipt requirement is
retained at `/mnt/data/bs2/simple-perf-final-9c/doc/08_tracking/bug/cross_language_actual_execution_mode_receipt_missing_2026-08-12.md`.

Until that run exists, the correct conclusion is: the diagnostic tables show
mode and workload shape, compiler speed remains unmeasured, Rust remains without
a retained numeric row, and no final Stage 4 performance result is available.
