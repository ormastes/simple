# Draw IR producer allocation counter is unavailable in the self-hosted runtime
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN

**Severity:** P2 — blocks complete AC-6 allocation evidence for retained Draw
IR producers

## Reproduction

Run the AC-6 producer receipt with the admitted self-hosted binary:

```sh
SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  bin/simple test \
  test/05_perf/graphics_2d/draw_ir_producer_storage_receipt_spec.spl \
  --mode=interpreter --assert-ran --no-session-daemon --sequential --no-db --no-cache
```

The receipt can retain actual frame-time and child-process RSS rows, but it
cannot obtain an authoritative allocation or array-capacity-growth delta for
the widget producer.

## Evidence

`src/compiler_rust/runtime/src/value/heap.rs` implements
`rt_heap_alloc_count` and `rt_heap_array_capacity_bytes`; the latter is the
needed live backing-buffer-capacity metric. They are not exposed by
`release/x86_64-unknown-linux-gnu/simple` (symbol inspection found neither).
The self-hosted core-C array grow operation is the private
`rt_core_array_reserve` in `src/runtime/runtime_native.c`, with no public
Pure-Simple facade. Existing `rt_mem_profile_features` only advertises header
bytes and hosted allocation metadata, not collection allocation counts or
array-capacity bytes.

## Required fix

Expose a stable, pure-Simple runtime facade for process-local collection
allocation/capacity evidence, at minimum a monotonic allocation count and live
array backing-buffer capacity bytes. It must be implemented by the admitted
self-hosted runtime as well as the bootstrap runtime, so a producer receipt can
take before/after deltas without a synthetic command-count estimate.

## Scope

Do not treat RSS, command counts, or modeled mimalloc counters as a substitute:
they do not identify actual language collection allocations in this workload.


## Re-check 2026-11-08 — fix-implemented-verification-pending
The required fix already exists at origin/release/1.0.0. It landed in `0f2712519c8` (2026-11-02,
"fix(runtime): real rt_heap_aux_live_bytes, core-C list completeness, link-completeness gate"):
- `src/runtime/runtime_native.c`: public `rt_heap_alloc_count()` (monotonic
  `rt_core_heap_total_allocs`) and `rt_heap_array_capacity_bytes()` (`g_core_array_cap_bytes`, maintained
  by the array reserve/free paths). Both are declared in `src/runtime/runtime.h:491,494` and mirror
  `src/compiler_rust/runtime/src/value/heap.rs:778,1043`.
- Pure-Simple facade: `heap_alloc_count()` / `heap_array_capacity_bytes()` in
  `src/lib/nogc_sync_mut/sffi/host.spl:396-410`, consumed by
  `test/05_perf/graphics_2d/draw_ir_producer_storage_receipt_spec.spl:63-67`.
- Specs: `test/01_unit/runtime/heap_collection_counters_core_test.c` (core-C) and
  `test/01_unit/runtime/heap_collection_counters_facade_spec.spl` (facade).

Evidence (Windows, 2026-11-08):
- clang compiles `runtime_native.c` together with the core-C test, with no undefined-symbol errors for the
  two counters. A full link needs the canonical runtime source set. Adding `runtime.c` by hand gives
  duplicate symbols, and the C test has no runner script in the tree.
- Under the seed interpreter, `heap_collection_counters_facade_spec.spl` FAILS 0/1 (`expected 0 to be
  greater than 0`). That is expected: seed-interpreted values do not go through the core-C heap
  registry. The facade only reports real deltas in a native/self-hosted binary.

Remaining to close: redeploy the self-hosted binary, then run the facade spec and the AC-6 receipt
natively and record non-zero allocation and capacity deltas.
