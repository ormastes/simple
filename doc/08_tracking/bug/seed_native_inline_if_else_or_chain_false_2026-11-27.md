# Seed native codegen: inline `if/else` whose else arm is an `or`/`and` chain evaluates false

- **Status:** open (codegen). Workaround landed in `src/app/cli/shard_worker_reap_v1.spl`
  (`shard_worker_reaped_stopped_v1`) — verification-pending.
- **Found by:** phase-ladder run 45916738302 (`9f757ab0a88`, linux-x86_64, fresh, rung 2).

## Symptom

Rung 1 built `build/bootstrap/stage1/simple` with the Rust seed. Rung 2's
`resolve-bootstrap-compiler` hello build with that stage1 failed every time:

```
[file-worker] done owner=0/2@0 units=1 module_scoped=true
[file-worker] owner=0/2@0 status=BLOCKED exit=0 claimed=1 sealed=-1 finished=true
[file-worker] inventory incomplete rows=-1 ...
[file-worker] aggregate failure exit=1 failed_modules=0 blocked=worker could not be reaped; link blocked
```

The worker did its work and exited 0. `sealed=-1` means the pool decided the
owner was NOT stopped (`native_build_main.spl`, file-worker reap), then
`process_kill` on the already-reaped pid could not confirm it, so the ledger
was blocked. Reproduced locally (WSL, stage1 artifact from the run) on a
one-file hello build.

## Root cause (minimal repro, seed-built native binary)

```
fn old_shape(label: text, hir_stopped: bool, pid: i64, code: i64) -> bool:
    var owner_stopped = if label == "hir-shard": hir_stopped else: pid <= 0 or (code != -2 and code != -1 and not process_is_running(pid))
    owner_stopped
```

Spawn `/bin/true`, poll `process_wait` to `code=0`: native output is
`running=false not_running=true owner_stopped=false`. Every operand is
right; the combined inline `if ..: a else: x or (y and z and not f())`
evaluates false. The interpreter gets it right, so the unit spec alone
cannot see it.

## Workaround

The reap site now uses plain statements (`shard_worker_reaped_stopped_v1`,
plus a statement-form liveness probe). Spec:
`test/01_unit/app/cli/shard_worker_reap_spec.spl` ("shard worker reap after
a real exit").

## Remaining

Fix the seed's native lowering of a value-producing inline `if/else` whose
arm is a short-circuit `or`/`and` chain, then remove the workaround tag.


## Shard Registration (2026-11-27)

- **Workaround site:** `src/app/cli/shard_worker_reap_v1.spl:217-229` (`shard_worker_reaped_stopped_v1`, tagged `# @workaround bug=seed_native_inline_if_else_or_chain_false_2026-11-27`).
- **Shard:** `doc/08_tracking/bug/db/seed_native_inline_if_else_or_chain_false_2026-11-27.sdn` (`status=open`, pending Rust seed native lowering fix for inline `if/else` short-circuit `or`/`and` chains).
