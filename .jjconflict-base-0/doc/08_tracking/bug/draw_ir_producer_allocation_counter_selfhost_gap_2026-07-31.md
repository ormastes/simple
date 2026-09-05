# Draw IR producer allocation counter is unavailable in the self-hosted runtime

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
