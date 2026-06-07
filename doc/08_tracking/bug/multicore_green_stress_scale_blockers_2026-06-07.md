# Multicore Green Stress Scale Blockers - 2026-06-07

## Summary

The cross-language stress profile now includes a Simple multicore-green native
row at 256 tiny workers with `pool_used=256/256` evidence. Two scale blockers
prevent using the previous 512-worker smoke size for the Simple row today.

## Evidence

- A generated 512-worker unrolled `multicore_green_spawn` stress source timed
  out during native compile under the profile smoke budget.
- A compact handle-array variant compiled and reported
  `multicore_green_pool_used = 512/512`, but failed checksum validation:
  `checksum_mismatch total=-549722803792 expected=546919154944`.
- Unrolled 64, 128, and 256 worker probes compiled and passed checksum
  validation. The 256-worker probe reported `pool_used=256/256`.

## Impact

- The checked-in smoke profile uses `FANOUT_STRESS_WORKERS=256` so Simple,
  Go, and C are measured with the same large stress count and the contract can
  reject invalid Simple rows.
- Larger stress counts remain valid future targets, but cannot be claimed until
  native compile scaling and compact handle-array join correctness are fixed.

## Follow-Up

- Reduce native compile cost for generated many-spawn Simple workloads.
- Investigate native codegen/runtime behavior for `[MulticoreGreenHandle]`
  arrays storing runtime-pool handles and later joining them.
