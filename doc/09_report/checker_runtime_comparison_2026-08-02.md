# Checker runtime comparison — 2026-08-02

## Result

The Rust implementation language is not the demonstrated cause of the slow
checker path.  The measured path starts the Rust bootstrap seed and asks it to
load and evaluate `src/app/check/main.spl`; source-closure startup alone takes
about 1.7 seconds and the 12-file parse/check workload takes 9.6–10.2 seconds
with one worker.  Python takes about 75 ms only for manifest validation,
SHA-256 verification, sharding, and process orchestration.  Python does **not**
parse Simple and is therefore an overhead bound, not a semantic competitor.

The pure-Simple native/dynload rows are pending.  The explicit-entry build
reached link in 23 seconds but the core C bootstrap did not provide
`rt_array_sort`, `rt_env_remove`, `rt_is_debug_mode_enabled`, or `rt_dir_list`.
No substitute binary or parse-only proxy was used.

## Reproducible fixture and method

- Manifest: `test/05_perf/checker_startup_manifest.tsv`
- Files: 12 fixed, valid `.spl` fixtures
- Manifest SHA-256:
  `3b392cff671f9275aba2b2765ca34d6811bf6114b66f9ba5032d4247ab6222c6`
- Harness: `scripts/bench/checker-performance.py`
- Evidence:
  `doc/09_report/evidence/checker_runtime_comparison_linux_2026-08-02.json`
- Host: Linux 6.8, AMD Ryzen Threadripper 1950X, 32 logical CPUs,
  Python 3.12.3
- Rust seed SHA-256:
  `e0a2fcc63bd3dc4ba27e0630b294208f1a984f0eab51621d973fdbabb2930bd5`
- Checker entry SHA-256:
  `b6a84359e311d298c1f398f27cd631a20f3e833588f65bea25e4021ad02dfb25`

“Cold” means fresh `SIMPLE_CACHE`, `SIMPLE_NATIVE_BUILD_CACHE_DIR`, and
`XDG_CACHE_HOME` directories.  “Warm” immediately repeats with the same
directories.  The harness does not drop the host page cache, so these are
logical-cache measurements, not physical cold-boot measurements.  Each cell
is one observation while other repository work was active; use it as a
baseline and blocker discriminator, not a publication-quality percentile.

Startup is a no-work process invocation (`--help` for source Simple; an empty
manifest for the native runner).  Total is a separate process group checking
all 12 files.  Four workers use four round-robin manifest shards.  Peak RSS is
the sampled process-tree sum with direct-child `ru_maxrss` as the short-process
lower bound.  Process count excludes threads and zombies.

## Measurements

| Engine | Cache | Workers | Startup | Total wall | Files/s | CPU | Peak RSS | Live processes | Outcome proof |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| Python orchestration only | cold | 1 | 75.9 ms | 75.7 ms | 158.52 | 92% | 18,944 KiB | 1 | N/A: no Simple semantics |
| Python orchestration only | warm | 1 | 74.6 ms | 74.3 ms | 161.41 | 83% | 18,944 KiB | 1 | N/A: no Simple semantics |
| Python orchestration only | cold | 4 | 79.2 ms | 78.0 ms | 153.80 | 317% | 75,776 KiB | 4 | N/A: no Simple semantics |
| Python orchestration only | warm | 4 | 79.2 ms | 79.2 ms | 151.51 | 325% | 75,520 KiB | 4 | N/A: no Simple semantics |
| Rust seed + interpreted Simple checker | cold | 1 | 1,676.4 ms | 9,582.8 ms | 1.252 | 100% | 233,960 KiB | 1 | exact, 12/12 |
| Rust seed + interpreted Simple checker | warm | 1 | 1,680.9 ms | 10,244.3 ms | 1.171 | 99% | 233,776 KiB | 1 | exact, 12/12 |
| Rust seed + interpreted Simple checker | cold | 4 | 2,013.3 ms | 4,865.2 ms | 2.466 | 353% | 932,548 KiB | 4 | exact, 12/12 |
| Rust seed + interpreted Simple checker | warm | 4 | 1,913.9 ms | 4,673.0 ms | 2.568 | 352% | 925,324 KiB | 4 | exact, 12/12 |
| Compiled pure-Simple native | cold/warm | 1/4 | **pending** | **pending** | **pending** | **pending** | **pending** | **pending** | link blocker |
| Cached pure-Simple dynload | cold/warm | 1/4 | **pending** | **pending** | **pending** | **pending** | **pending** | **pending** | same blocker |

The Rust-source outcome checksum is identical in all four cells:
`0719b23f610a2abbc610fd650de9ef16e056254a7291d1d4458c24721e0bb4e4`.
It covers sorted file id, path, source digest, normalized status, and exit code.
All 12 outcomes are `ok`/exit 0.  The Python checksum
`2cc2b3415727897678e3976f4e68c3de833ecb455f5cdbb613139ff506e5112d`
is intentionally different because its status is `orchestration_ok`; it cannot
be used as compiler-semantic parity evidence.

At one worker, source-Simple startup is about 22 times the measured Python
driver startup and total check wall time is about 127 times Python
orchestration.  Those ratios isolate avoidable loader/evaluator work; they do
not show that Python can perform the same check faster.  Four source workers
raise throughput 1.97 times over the cold one-worker row, while using 3.99
times the peak RSS.  This makes process fan-out a throughput/RSS tradeoff, not
the primary startup fix.

This benchmark covers the parse/check preflight in `src/app/check/main.spl`.
It does not prove HIR, MIR, code generation, artifact creation, or artifact
execution.  Those remain the diagnostic two-phase pipeline's responsibility.

## Native/dynload resume command

After the four missing bootstrap runtime symbols are available and the runner
accepts an empty manifest, run:

```bash
export SIMPLE_STAGE4_DIAG_CHECK_RUNNER=/absolute/path/to/checker-runner
python3 scripts/bench/checker-performance.py \
  --engine=pure-simple-native,pure-simple-dynload \
  --manifest=test/05_perf/checker_startup_manifest.tsv \
  --workers=1,4 \
  --cache-states=cold,warm \
  --compiler-digest=<full-compiler-closure-sha256> \
  --timeout=120 \
  --output=doc/09_report/evidence/checker_runtime_comparison_native_linux.json
```

Accept the result only when every native/dynload row contains 12 terminal
outcomes and reproduces the Rust-source checksum above.  Normalize terminal
rows by id/path/source digest/status/exit code; ignore elapsed time and physical
artifact path when checking parity.

