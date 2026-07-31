# Draw IR producer storage receipt (AC-6)

Run:

```sh
SIMPLE_BIN=bin/release/<triple>/simple SIMPLE_LIB=src bin/release/<triple>/simple test \
  test/05_perf/graphics_2d/draw_ir_producer_storage_receipt_spec.spl \
  --mode=interpreter --assert-ran --no-session-daemon --sequential --no-db --no-cache
```

Step: `Reuse producer storage across frames`.

The executable receipt builds the canonical widget Draw IR producer at 64,
1,000, and 10,000 commands. For each scale it records in-process frame time
(`ns/op`) through `bench_run_warm_ns` and process peak resident set size
(`rss_kb`) through `bench_run_process_rss`. The RSS child workload is
`test/05_perf/graphics_2d/draw_ir_producer_storage_workload.spl`.

The child runtime is the explicit admitted pure-Simple `SIMPLE_BIN`; bootstrap
seed paths are rejected. Each scale retains a Markdown receipt and metrics table
through the existing `bench_emit` convention under
`build/test-results/draw-ir-producer-storage/`; their existence is asserted by
the executable scenario. RSS availability is mandatory: a platform that
reports `rss_kb(unavailable)` fails the receipt rather than silently satisfying
AC-6.

`expect_producer_allocation_budget` is the exact frozen allocation helper. It
records `unavailable:no-runtime-allocation-counter`: the current runtime has
no allocation counter exposed to this producer tier, and the scenario does not
substitute command counts or estimates. Consequently AC-6 has real frame-time
and RSS evidence but remains **partial** until an authoritative allocation
metric is available. The concrete self-hosted runtime gap is tracked in
[`draw_ir_producer_allocation_counter_selfhost_gap_2026-07-31.md`](../../../08_tracking/bug/draw_ir_producer_allocation_counter_selfhost_gap_2026-07-31.md).

The producer itself retains and appends through existing mutable command and
batch collections; no new collection type or Web layout-framework ownership is
introduced by this receipt.
