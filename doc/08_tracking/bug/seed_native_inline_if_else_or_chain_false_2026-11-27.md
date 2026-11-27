# Seed native codegen: inline `if/else` whose else arm is an `or`/`and` chain evaluates false

- **Status:** verification-pending (import ABI fix: f63e2e35906d + PR 12278). Workaround in `src/app/cli/shard_worker_reap_v1.spl`
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

## Original hypothesis (superseded -- see "Real root cause")

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

## Real root cause (2026-11-28)

Not if/else or short-circuit lowering. Reproduced on linux-x86_64 with a
pre-f63 seed (WSL, `/home/dev/ssos-seed-target/release/simple`, Nov 22):
`g1`/`g3`/`g5` shapes read false, while bool-cond, single-`and`, no-call and
no-outer-`or` variants read true. SIMPLE_DUMP_MIR of the failing function
was correct. SIMPLE_DUMP_CLIF of `_process_is_running_raw` showed the import
`rt_process_is_running` declared `(i64) -> i64`, but the C runtime returns
`bool`. Its disassembly ends `sete %bl; movl %ebx, %eax`, so bits 8..31 of
the caller's saved RBX leaked into the result. `not process_is_running(pid)`
is `icmp_imm eq v, 0` on the full word, so it reads false whenever RBX had
nonzero bits. The if/else shape only changed register allocation, which is
why it looked like a lowering bug and why the interpreter was right.

- Fix: `RUNTIME_FUNCS` declares C/Rust `bool` returns as I8.
  `f63e2e35906d` (rt_process_is_running/kill/exists, landed after the ladder
  seed `9f757ab0a88`) plus this change (rt_driver_cancel,
  rt_driver_supports_sendfile, rt_driver_supports_zero_copy).
- Guard: `runtime_h_bool_returns_use_i8_abi` (runtime_sffi.rs tests) fails on
  any `bool rt_*` prototype in `src/runtime/runtime.h` whose spec is not I8.
- Pure-Simple backend: already safe. Cranelift adapter re-extends narrow
  import results by declared return (`cl_import_result_narrow_plan`), and
  LLVM declares externs with their declared `i1` return.
- Terminal lane gap closed (2026-11-28, owner decision): the core-C native
  link uses `runtime_terminal.c` (C `bool`), simple_core's twins and every
  `.spl` caller are `-> bool`. Only the Rust provider was a tagged
  `RuntimeValue`. Tagging C would have broken the raw-bool callers, so the
  Rust provider now returns plain `bool` and all four specs are I8.
  `runtime_h_bool_returns_use_i8_abi` has no exceptions.

## Remaining

The `@workaround` stays until a Linux seed carrying f63e2e35906d and this
change is redeployed and the phase-ladder rung 2 hello build passes natively.

## Shard Registration (2026-11-27)

- **Workaround site:** `src/app/cli/shard_worker_reap_v1.spl:217-229` (`shard_worker_reaped_stopped_v1`, tagged `# @workaround bug=seed_native_inline_if_else_or_chain_false_2026-11-27`).
- **Shard:** `doc/08_tracking/bug/db/seed_native_inline_if_else_or_chain_false_2026-11-27.sdn` (`status=open`, pending Rust seed native lowering fix for inline `if/else` short-circuit `or`/`and` chains).
