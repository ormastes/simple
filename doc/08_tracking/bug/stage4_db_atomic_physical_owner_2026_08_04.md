# Stage 4 db_atomic physical-owner gap

## Status

Resolved in source on 2026-08-04; production Phase 4 crossed this module in the
next bounded session.

## Symptom

The final cycle crossed duplicate-check threshold parsing, the production test
runner, and CLI run/fix command ownership. HIR lowering then stopped in
`src/lib/nogc_sync_mut/db_atomic.spl` on unresolved `_`, `file_atomic_write`,
`file_lock`, `file_unlock`, and `parse`.

## Evidence

- Log: `build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build-cli-run-owner-cycle3.log`
- Elapsed: 3m08.62s
- Peak RSS: 1,416,128 KiB
- Stub fallback: disabled
- LLVM provider: repository-managed 23.1.0-rc2 prefix

## Repair and evidence

The module now imports physical nogc-sync file, sysinfo, and time owners; hoists
the canonical common-SDN parser/value owners; replaces unsupported point-free
row mapping with an explicit loop; and consumes the current two-field
`SdnValue.Table` payload. The focused native contract crossed HIR/object
generation and stopped only at the narrow core bundle's missing
`rt_file_atomic_write`. Production cycle 1 crossed the repaired module and
advanced to `compile_targets.spl`.
