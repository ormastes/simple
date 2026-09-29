# Startup Perf-Budget Lane

Guards `bin/simple` startup latency: p50 of N=7 runs of `bin/simple --version`
and `bin/simple run test/05_perf/startup/hello_fixture.spl`, compared against
committed budgets in `budgets.sdn`.

Run:

```bash
sh scripts/check/check-startup-perf-budget.shs            # fatal selftest, then measure
sh scripts/check/check-startup-perf-budget.shs --selftest # fixtures only
```

Verdict (last stdout line, detector standard —
`doc/07_guide/infra/detector/detector_standard.md`):

- `PASS — 2 command(s) measured (N=7, binary=<seed|self-hosted> <path>): ...` exit 0
- `SKIP — bin/simple missing/unresolvable ...` exit 0 (explicit, never a measurement)
- `FAIL — ... <which> p50=<measured>ms > budget <n>ms` exit 1
- `ERROR — nothing was checked ...` exit 2 (missing budgets file, failed runs, failed selftest)

The verdict records binary identity (rust-seed vs self-hosted) because the two
have very different startup profiles — never compare timings across identities.

## Updating budgets (the ONLY recorded escape)

Edit `budgets.sdn` and change the value **with a dated comment** explaining the
new measurement and why. There is deliberately no env var or flag override —
a silent override is exactly the escape the detector standard forbids. Budgets
are set at measured p50 x3 so shared-box noise does not flap the lane
(2026-08-18 baseline: version 122ms, run-hello 133ms, seed binary).

Status: ADVISORY (FP rate not yet adjudicated on a named sample; see FP-RATE
line in the script header before any promotion to blocking).

## Interpreter identifier-hash memo

`scripts/check/check-interpreter-hash-memo-perf.shs` measures an explicitly
owned eight-entry memo against the stateless FNV-1a function. It includes hot,
4,096-name miss-heavy, product-shaped LOAD_FAST, and module/global slow-env
fixtures. Evidence is N>=7 and interleaved, with exact binary/source/harness/
tool/host identities and raw elapsed/RSS/stdout/stderr hashes.

This collector is deliberately fail-closed: a Rust seed, missing/invalid
adjacent Stage4 provenance, or a raced identity exits 2 and writes no receipt.
See `doc/10_metrics/startup/interpreter_hash_memo_perf_2026-08-19.md`.

## Class A cross-language matrix

`scripts/check/check-startup-class-a-matrix.shs` measures startup after all
preparation has completed for Simple native, C, Rust, Go, Python, Bun, and
Java. Each lane prints the same exact checksum, runs at least one warmup and
seven timed samples, and records raw samples, p50, p95, maximum RSS, compiler
and executable hashes, execution mode, and fallback status in an immutable
retained-schema receipt under `build/perf/startup_class_a_v2/`.

The matrix never substitutes another runtime. A missing compiler/runtime or
missing pure-Simple self-host is `unavailable`; a present lane with a build,
checksum, sampling, or receipt failure is `rejected` and makes the matrix
fail. A global PASS additionally requires the pure-Simple native subject to be
admitted; competitor rows cannot make a missing Simple row pass. The schema
selftest has exactly 18 biting controls: fallback, sample floor, budget policy,
p50 budget, p95 budget, RSS budget, order seed, order position, missing raw
row, recomputed percentile, maximum RSS, hash, self-host status, startup class,
ratio, rustup identity, Rust host, and bound-tool version. Stage 4 is currently
unavailable, so the full matrix has not run and no v2 matrix receipt exists.
Run the schema contract independently with:

```bash
sh test/05_perf/startup/class_a/startup_class_a_schema_contract_test.shs
```

## dynSMF production trust cutover

`dynsmf_trust_cutover_source_closure_spec.spl` is the non-timing closure gate
for the startup-sensitive trust cutover. It keeps empty/help/version returns
ahead of OS trust-config admission, rejects process/compiler/directory-scan
dependencies in the registry owner, and proves ordinary/component registry
branches consume retained bytes rather than reopening executable paths.

Run it together with the existing argument-parser/mmap startup regression:

```bash
SIMPLE_LIB=src <diagnostic-simple> test test/05_perf/startup/dynsmf_trust_cutover_source_closure_spec.spl --mode=interpreter --fail-fast
SIMPLE_LIB=src <diagnostic-simple> test test/02_integration/app/startup_argparse_mmap_perf_spec.spl --mode=interpreter --fail-fast
```

These commands are focused source/interpreter evidence. They do not establish
Stage 4, native latency/RSS, bootstrap convergence, or release readiness.
