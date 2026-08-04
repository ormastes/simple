# Stage 4 db_atomic physical-owner gap

## Status

Open; retained after the third and final bounded x86 Phase 4 cycle on
2026-08-04.

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

## Next action

In a fresh bounded session, identify the physical file-lock/atomic-write and SDN
parse owners, reproduce the local wildcard binding that yields unresolved `_`,
and repair only `db_atomic.spl` plus a focused native contract. Do not widen HIR
resolution, add runtime aliases, or start a fourth production retry in the
exhausted session.
