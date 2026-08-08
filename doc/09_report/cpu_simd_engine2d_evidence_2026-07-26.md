# CPU SIMD Engine2D AArch64 Evidence — 2026-07-26

## Status

`BLOCKED`: the scalar normalization and evidence-integrity repair are ready,
but no provenance-complete native acceptance run was performed in this review.

The lane already contains three native-build artifacts from the earlier
diagnosis:

1. `cpu_simd_engine2d_evidence`
2. `cpu_simd_engine2d_evidence_fixed`
3. `cpu_simd_engine2d_evidence_receipt`

A fourth native build would violate the mandatory three-cycle cap. The earlier
artifacts do not count as acceptance evidence because their exact compiler,
source revision, source hash, build command, build exit, executable hash, run
exit, and bounded raw logs were not retained together.

## Implemented Repair

- `_scalar_blend_row` normalizes packed source and destination words to `i64`
  before bit arithmetic.
- The committed
  `scripts/build/cpu-simd-engine2d-evidence/cpu_simd_engine2d_evidence.spl`
  file is the only evidence program. The wrapper copies it and requires
  byte-for-byte equality plus equal SHA-256 before execution.
- The non-opaque alpha fixture covers source alpha `0`, `1`, `127`, `128`,
  `254`, and `255`, with transparent, translucent, and opaque destinations.
- Acceptance derives from explicit hit counters and exact mismatch totals,
  not aggregate bool storage or diagnostic reason text.
- Native mode now fails closed unless it records the Git revision, canonical
  and copied source SHA-256 values, compiler SHA-256, exact build command,
  build exit, executable SHA-256, exact run command, run exit, and bounded
  build/run logs with their SHA-256 values.

## Superseded Claims

The previous before/after checksum narrative is withdrawn as acceptance
evidence because it was not bound to a complete retained provenance record.
It must not be used to approve or release this lane.

## Next Native Cycle

In a fresh verification session, run exactly one native cycle through:

```sh
SIMPLE_CPU_SIMD_EXECUTION_KIND=native \
BUILD_DIR=build/cpu-simd-engine2d-evidence-native \
REPORT_PATH=doc/09_report/cpu_simd_engine2d_evidence_2026-07-26.md \
sh scripts/check/check-cpu-simd-engine2d-evidence.shs
```

The resulting report is acceptable only when status is `pass`, source equality
is `pass`, all required hashes are present, both native exits are `0`, both
logs are bounded, native SIMD hits are positive, and all exact bitmap mismatch
counts are zero. The wrapper fails if no Engine2D-SIMD-capable pure-Simple
compiler is available; deploy one before starting that fresh cycle.
