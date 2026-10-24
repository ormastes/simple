# MIR/HIR shard coordinator relaunches workers with nothing left to claim

Symptom: both MIR shard workers crashed after claiming and sealing all 735
modules (`status=CRASH exit=-134 claimed=735 sealed=735`); the coordinator still
launched `SIMPLE_MIR_SHARD_OWNER=0/2@1` and `1/2@1`. Each reloaded ~6 GB of HIR
for no work (~1 h wasted).

Root cause: `hir_shard_recovery_can_replace` (src/compiler/80.driver/driver_hir_recovery.spl)
only checked `new_claims > 0`, i.e. that the dead worker made progress.

Fix: new `hir_shard_recovery_unclaimed_count` counts inventory rows with no claim;
`can_replace` takes it and requires `unclaimed > 0` (unreadable = -1 = no
replacement). Call site: `run_ledger_shards` in src/app/cli/native_build_main.spl.
With no replacement the loop falls through to `close_inventory` and the normal
failure aggregation. Real recovery (claims remain) is unchanged.

Verification: spec cases added in
test/03_system/compiler/driver/hir_shard_recovery_spec.spl, UNEXECUTED.
