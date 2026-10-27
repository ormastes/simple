# One crashed HIR shard blocks the whole ledger (misleading "claim" reason)

**Status:** fixed (2026-10-27, branch `work/hir-claim-reason`; the OOM in shard 6 itself is out of scope)

## Symptom

Whole-program native-build, 8 HIR shards (`C:/dev/p3new/buildwp3.log`, `.log.err`,
ledger `cachewp3/default/frontend/queue-10220-0`). At ~313 s shard 6/8 aborted
with `memory allocation of 6291456 bytes failed` before claiming anything. Every
other shard then logged
`[hir-shard] failed shard=k/8 claimed=N reason=HIR claim or cache identity unavailable`
-> `HIR shard ledger claim failed`; the coordinator sealed 1405 unfinished
modules BLOCKED and reported `HIR aggregate failure`.

## Evidence

`buildwp3.log.err` order:

```
2:  memory allocation of 6291456 bytes failed
22: [hir-shard] owner=6/8@0 status=CRASH exit=-1073740791 claimed=0 sealed=0 finished=false
23: [hir-shard] failed shard=0/8 claimed=18 reason=HIR claim or cache identity unavailable
27: [hir-shard] failed shard=2/8 claimed=7  reason=HIR claim or cache identity unavailable
...
```

The coordinator reaped 6/8 (CRASH, 0 claims) *before* any other shard failed.

## Cause (confirmed from log order + code)

Not a lock timeout. The coordinator itself wrote the global BLOCKED marker:
`src/app/cli/native_build_main.spl` reap path blocked the ledger on
`not finished and progress == 0`, which matches a worker that crashed before its
first claim. Every live shard's next `hir_shard_begin`
(`driver_hir_cache.spl`) then saw `hir_shard_recovery_blocked(queue)` and
returned `-1`, indistinguishable from a real claim failure, so the lowering
callers reported "HIR claim or cache identity unavailable" and
`hir_shard_recovery_block` *overwrote* the coordinator's BLOCKED text with that
misleading reason.

## Fix

- `driver_hir_recovery.spl`: claim returns named codes
  (`HIR_SHARD_CLAIM_{INVALID_ARGS,LOCK_TIMEOUT,PUBLISH_FAILED,INVALID_CLAIM,LEDGER_BLOCKED}_V1`
  = -1..-5) with `hir_shard_claim_reason_v1`; the ledger lock is retried
  3 x 30 s (`hir_shard_lock_with_retry`); `hir_shard_recovery_block` keeps the
  first BLOCKED reason; new pure decision
  `hir_shard_recovery_reap_blocks_ledger_v1` exempts a crash (`code < 0`) with
  0 claims and 0 sealed from blocking — nothing to seal, its rows stay claimable
  by live workers, the worker still counts as failed (aggregate non-zero).
  Every other incomplete shape (clean exit unfinished, positive exit with no
  claims, unreadable ledger, corrupt claim) still blocks fail-closed.
- `driver_hir_cache.spl`: `hir_shard_begin` returns `LEDGER_BLOCKED` when the
  ledger is blocked; `hir_shard_claim_failure_reason_v1(claim, path)` names the
  cause and module path.
- `driver_hir_pipeline_lowering.spl` (streaming + legacy claim sites): guard
  block / `add_error` carry that reason.
- `native_build_main.spl`: coordinator BLOCKED text names owner/exit/claimed/
  sealed/finished; HIR-aggregate go-to-end continuation also honours
  `SIMPLE_NATIVE_GO_TO_END=1` (previously only the `--go-to-end` argv).

Spec: `test/01_unit/compiler/driver/hir_shard_claim_reason_spec.spl`.

## Workaround (current stage2, pre-fix)

`SIMPLE_HIR_SHARDING=0` plus `--go-to-end` (or `SIMPLE_NATIVE_GO_TO_END=1`
together with `--go-to-end`; pre-fix the env alone did not pass the HIR
aggregate).

## Census: where one failure stops the whole native-build

| Stop point (file:line) | Keep-going knob | Sharded HIR path | In-process whole-program path | Gap |
|---|---|---|---|---|
| HIR shard aggregate, `src/app/cli/native_build_main.spl:2017-2026` | `--go-to-end` / `SIMPLE_NATIVE_GO_TO_END=1` (go_to_end.spl:39) | yes: continues to final worker which redoes HIR for failed modules | n/a | env-only knob was ignored here — fixed |
| HIR worker reap -> global BLOCKED, `native_build_main.spl:1116` | `--keep-going` (fail_fast=false) only affects replacement/kill, not BLOCKED | BLOCKED stops all peers' claims | n/a | 0-claim crash blocked everyone — fixed |
| HIR worker fail-fast kill, `native_build_main.spl:1120` | `--keep-going` / `SIMPLE_COMPILE_FAIL_FAST=0` (compile_failure_policy.spl:3) | yes | n/a | none |
| In-process HIR/analyze failure, `driver_orchestration.spl:526,638` | go-to-end | n/a | yes (drops failed modules + importers) | none |
| MIR lowering, `driver_pipeline_lowering.spl:296,420,842,877` | go-to-end, `ice_boundary_keep_going` | n/a | yes | none |
| MIR shard aggregate, `native_build_main.spl:1417` (opt-in `SIMPLE_MIR_SHARDING=1`) | none | link blocked | n/a | no go-to-end continuation; go-to-end never links anyway, so use in-process MIR (`SIMPLE_MIR_SHARDING=0`) — not implemented |
| AOT/codegen batch flush, `driver_aot_pipeline.spl:178,216,310,762` (`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH`) | go-to-end | n/a | yes (records per-module, excludes) | none |
| File-worker aggregate, `native_build_main.spl:1520` | none | link blocked | n/a | same as MIR shard aggregate |
| Link / publish, `driver_aot_native_output.spl:3067` | go-to-end writes manifest, never links, exits non-zero | — | yes | by design |
