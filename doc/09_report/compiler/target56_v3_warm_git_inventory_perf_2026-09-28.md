# Target 6 V3 warm Git inventory paired native cohort (2026-09-28)

**Status: performance gate unresolved.** This is a focused inventory bridge
measurement, not a full compiler or MCP/LSP cohort. The requested normalized
time/RSS sum is 2.032, above the 2.000 limit; the sample does not establish a
regression outside noise either. Keep the PR in draft.

## Reproduction and provenance

- Same workload source: `test/05_perf/scv/git_inventory_warm_workload.spl`.
- Pre-V3 baseline: detached `93cbe7f31bc`; candidate: `3405fd215fe` plus the
  identical, initially untracked workload source. Both built with the admitted
  pure-Simple Stage2 compiler SHA-256
  `d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
- Both builds used `SIMPLE_NO_STUB_FALLBACK=1`,
  `SIMPLE_SCV_FREEZE_FALLBACK=1`, `native-build --source src/compiler --source
  src/app --source src/lib --entry-closure --entry
  test/05_perf/scv/git_inventory_warm_workload.spl`. Each compiled 83 units
  without stubs. The baseline/candidate binary SHA-256 values are
  `3ebd8c4ea31a368f8df9dad790173b9b2edaecc632e79aff8e66a9d08c5474b3`
  and `4ca6dd6d730dec82daaf8f11060f8b429ea622fe85612f76a09976c55b43acea`.
- Each binary prepared its own committed 1,200-source Git fixture and admitted
  a cold inventory outside timing. Both fixtures have Git tree
  `9c4f00a4f18a8f2c1e560279f7652fcecdc706bd`. Thirty separate warm
  processes per binary were alternated, with order reversed every pair.
  `warm_ns` times the refresh only; process wall includes launch and inventory
  readback. `/usr/bin/time` supplied peak process RSS. The complete 60-row
  record is `target56_v3_warm_git_inventory_samples_2026-09-28.tsv`, SHA-256
  `74fe0c25381c0e39c88d1c457dca952ece6c6e882a46c60285adf3eaf8d89e5b`.

| Measure | Pre-V3 | V3 | V3 / pre-V3 |
|---|---:|---:|---:|
| Warm refresh p50 | 87.966 ms | 91.831 ms | 1.044 |
| Warm refresh p95 | 98.480 ms | 101.799 ms | 1.034 |
| Peak process RSS | 27,392 KiB | 27,344 KiB | 0.998 |
| Process wall p95 | 125.803 ms | 179.175 ms | 1.424 |
| Binary size | 233,496 B | 249,240 B | 1.067 |
| Native build peak RSS | 286,112 KiB | 313,696 KiB | 1.096 |

The warm p95 + peak RSS ratio sum is **1.033709 + 0.998248 = 2.031957**.
The paired median warm difference is +1.567 ms; a 10,000-resample paired
bootstrap 95% interval spans -1.601 to +7.849 ms. The candidate's process
wall p95 includes a high outlier. Neither the p95 increase nor a claim of
equivalence is established by this sample. The workload has no untracked
source paths, so it specifically measures the cost of V3 on an unchanged
warm inventory. It does not exercise the new create/delete behavior.

## Required follow-up

Retain the raw samples and workload for review. Diagnose the warm time and
process startup spread, then optimize V3 or gather a controlled cohort that
meets the normalized sum rule. Run a production-size compiler/MCP/LSP fixture
after the typed graph publisher and full entrypoint cutover exist. The extra
15,744 binary bytes are attributable to this focused V3 closure; Target 5's
release-small size/startup gate remains separate and open.
