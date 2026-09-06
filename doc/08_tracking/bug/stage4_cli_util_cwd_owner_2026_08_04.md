# Stage 4 CLI utility cwd owner

## Status

Source fixed; focused native contract PASS; exact Phase 4 verification pending.

## Symptom

Fresh exact x86 Phase 4 cycle 1 crossed the database time/process owner repair,
then HIR lowering stopped in `src/lib/nogc_sync_mut/cli/cli_util.spl` on
unresolved `cwd`.

## Evidence

- Log: `build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build-database-owner-cycle1.log`
- Elapsed: 14m55.75s
- Peak RSS: 13,325,392 KiB
- Stub fallback: disabled
- LLVM provider: repository-managed 23.1.0-rc2 prefix

## Repair boundary

Bind cwd and file operations to their physical nogc-sync IO owners, preserve
the existing CLI argument and exit behavior, and do not widen HIR resolution or
add runtime aliases. Refresh the existing CLI utility source/behavior contract
where available, then use the second cache-preserving Phase 4 cycle.

The focused `stage4_cli_util_owner_contract.spl` compiled and linked with stub
fallback disabled, then exited 30 with empty output. Evidence is retained under
`build/focused/stage4-cli-util/`. Its deliberate first form exited 41 because
the repository root has no package manifest; the accepted contract checks the
documented empty-manifest result plus quoted CSV behavior.
