# Rust-hosted and pure-Simple checker optimization plan — 2026-08-02

## Goal and boundary

Make `simple check` use a cached compiled pure-Simple checker and load/evaluate
only what the request needs.  Preserve the 12-file per-file outcomes and exit
codes recorded in
`doc/09_report/checker_runtime_comparison_2026-08-02.md`.

The Rust seed remains bootstrap-only.  Rust-side work improves bootstrap and
diagnostic source execution; it is not the production fallback.  The checker
is a parse/check preflight, not proof that HIR/MIR/codegen or artifact semantic
validation completed.

## Optimization 1 — content-addressed checker closure

### Pure-Simple production path

1. Compute a closure key from target triple, checker entry digest, every
   transitive module digest, compiler/runtime ABI digest, optimization mode,
   and native/dynload mode.
2. Build the checker once into the caller-owned cache.  Publish with an atomic
   rename only after link and an empty-manifest startup probe pass.
3. Make the production wrapper resolve that exact key and execute the cached
   native artifact.  Raw `run src/app/check/main.spl` is an explicit developer
   mode, never the production hot path.
4. Reject partial, stale, or ABI-mismatched artifacts.  On a cache miss, build
   once under a per-key lock; concurrent callers wait for or reuse that build.
5. Retain the manifest/result contract:
   `<runner> --manifest=<path> --result=<path>
   --compiler-digest=<hex> --mode=<native|dynload>`.

### Rust bootstrap/source path

1. Cache the parsed/import-resolved checker graph by the same content inputs,
   plus seed build digest and parser feature flags.
2. Store immutable module parse products once.  Reset only per-file mutable
   parser state; do not rescan or reread unchanged closure modules per file.
3. Invalidate a module and its reverse-dependency slice on content change,
   compiler/ABI change, or mode change.  Never use mtime alone.

This optimization directly attacks the measured ~1.68-second source startup
and repeated closure work.  It precedes process fan-out because four source
workers currently multiply RSS from ~234 MiB to ~925 MiB.

## Optimization 2 — lazy dynload/eval with a reusable manifest worker

### Pure-Simple production path

1. Start a small manifest runner without loading the checker closure.
2. Validate id/digest/path rows first.  If the manifest is empty, exit without
   dynloading the checker; this is the startup probe and proves true laziness.
3. On the first valid source row, dynload the cached checker exactly once per
   worker.  Reuse it for the worker's remaining shard.
4. Lazily resolve optional checker modules only when the relevant file class or
   lint requires them.  Keep mandatory parser/check modules eager after first
   use so behavior is deterministic.
5. Reuse bounded read buffers and immutable closure tables.  Call the existing
   AST/parser reset between files and prove that no diagnostic state leaks.
6. Keep native and dynload outcome ordering deterministic by sorting terminal
   rows by manifest id/path before parity hashing.

### Rust bootstrap/source path

1. Add a manifest request mode to the evaluator so one Rust process loads the
   checker closure once and checks its whole shard.
2. Resolve imports on first symbol use and memoize both successful and failed
   resolution by module digest.  Do not shell out or scan the full tree in a
   per-file hot loop.
3. Bound worker lifetime by manifest/compiler digest.  Discard the process on
   ABI or closure-key change instead of attempting unsafe cross-version reuse.

This optimization separates the small orchestration layer from actual Simple
semantics and avoids both one-process-per-file startup and eager loading for
empty or irrelevant requests.

## Evidence-derived acceptance gates

All targets below come from the retained 2026-08-02 rows; they are initial
gates, not invented C/Python-parity claims.

1. **Behavior:** native and dynload each produce 12 terminal outcomes with
   checksum
   `0719b23f610a2abbc610fd650de9ef16e056254a7291d1d4458c24721e0bb4e4`.
   Every file is `ok`, exit 0, in cold/warm and 1/4-worker runs.
2. **Startup improvement:** native and dynload startup are below the fastest
   recorded Rust-source startup, 1,676.4 ms.  An empty manifest must not load
   or evaluate the checker closure.
3. **One-worker wall improvement:** total is below the fastest recorded
   Rust-source total, 9,582.8 ms; throughput therefore exceeds 1.252 files/s.
4. **Four-worker wall improvement:** total is below 4,673.0 ms; throughput
   therefore exceeds 2.568 files/s.
5. **RSS non-regression:** one-worker peak is below 233,776 KiB and four-worker
   peak is below 925,324 KiB.  A cached artifact is not accepted if it merely
   trades startup for higher peak memory.
6. **Process topology:** peak live process count is exactly the configured
   external worker count (1 or 4); no per-file child process is allowed.
7. **Cache behavior:** cold and warm use the same artifact key; the warm row
   reports a hit and performs no compile/link.  Editing one manifest source
   invalidates only its source result, while editing a closure module changes
   the closure key and invalidates the checker artifact.
8. **Scope honesty:** Python remains `semantic_parity=not_applicable`; Phase A
   compile and Phase B artifact execution are reported separately.

Run three native/dynload benchmark repetitions after the artifact exists and
apply gates 2–5 to the median.  Retain all raw JSON files so host load and
variance remain visible.

## Execution order

1. Supply the four missing core C bootstrap runtime symbols and rebuild the
   explicit checker entry.
2. Implement and test the content-addressed closure artifact/cache.
3. Implement empty-manifest laziness and first-row dynload/eval.
4. Add invalidation and concurrent single-builder tests.
5. Run the fixed manifest at 1 and 4 workers, cold and warm, then verify exact
   checksum parity before considering performance numbers.
6. Run diagnostic Phase A/B separately; do not promote preflight success to a
   completed build.

