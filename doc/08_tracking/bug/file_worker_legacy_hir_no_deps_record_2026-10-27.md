# File-worker: legacy HIR path publishes no deps record, so every worker blocks (2026-10-27)

**Status:** fixed (work/hir-shard-deps-legacy-path)
**Evidence:** `C:/dev/p3new/build2.log` (stage2 e4746b05, 8 workers): `has no deps record; MIR not admitted`, `status=BLOCKED exit=1` for 8/8 workers, 0 objects. The HIR ledger had PASS terminals but no `.deps` or `.hirkey` files.

## Cause
`hir_shard_publish_deps_v1` / `hir_shard_publish_hirkey_v1` ran only in the streaming HIR path
(`driver_hir_pipeline_lowering.spl` ~1263). Shard children route to the legacy
`lower_and_check_retained_owner_impl` unless `SIMPLE_STAGE3_STREAMING_SURFACES`, stage4 or low_memory is set
(`driver_phase_gates.spl:83`). The legacy path claims a module (~1884), lowers it and writes PASS, but publishes
neither record, so the worker can never admit MIR.

## Fix
Both paths publish through one helper, `hir_shard_publish_records_v1`, and take their edges from
`hir_shard_dep_source_indices_v1`. The coordinator now prints `[file-worker] first-error owner=<o> <reason>`.

## Why not route children through streaming
Measured 2026-10-27 (`C:/dev/p3new/build3.log`): with `SIMPLE_STAGE3_STREAMING_SURFACES=1`, 5 workers reached
62.9 GB and were killed before any claim (`claimed=0 sealed=-1`). Streaming-surface HIR children peak at about
12 GB each before claiming, so streaming is not a viable worker route until that cost is cut.
