# Layout Framework Guide — TLDR

- Full run is the CPU geometry oracle baseline.
- Incremental runs require explicit dirty islands and return visited ids.
- Cycles are bounded; non-convergence is explicit.
- GPU receipts require a cost-winning homogeneous block/flex/grid batch.
- Browser integration stays outside the common framework.

<!-- sdn-diagram:id=layout-framework-guide-tldr -->
```sdn
operator: [full_baseline, incremental_dirty_run, inspect_receipt]
```
