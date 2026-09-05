# Lane IPCREPLY — kernel reply object on the syscall path

Master plan row: `ipc:` (Phase 1) — "full endpoint/reply/notification fastpath +
two-process QEMU call/reply evidence".

## What landed (this lane)

- `src/os/kernel/ipc/reply_object.spl` — the reply object / reply capability
  mechanism in L4-seL4 terms:
  - `ReplyTable.call(caller, receiver)` mints ONE single-use reply capability and
    marks the caller blocked.
  - `ReplyTable.notify(caller, receiver)` is non-blocking and mints NO reply cap;
    a reply against it is refused with `REPLY_ERR_NOT_A_CALL` (-3), distinct from
    `REPLY_ERR_NO_SUCH` (-1) for an unknown id.
  - `ReplyTable.reply(...)` consumes the one-shot; the second reply is denied
    with `REPLY_ERR_ALREADY_REPLIED` (-2).
  - `ReplyTable.mark_task_dead(tid)` INVALIDATES (burns) the caller's live reply
    caps so they never dangle; a later reply gets `REPLY_ERR_CALLER_DEAD` (-4).
  - Handle transfer on reply: attenuated, deny-wins
    (`REPLY_ERR_RIGHTS_ESCALATION`, -6), and ATOMIC (trial mint against a
    throwaway ledger, commit only when the whole batch is authorized).
- `test/01_unit/os/kernel/ipc/reply_object_spec.spl` — 5 describe blocks,
  33 examples, absolute-oracle assertions (exact status codes, exact cap-set
  contents — never "not an error").

## Evidence (2026-07-27)

GREEN, A/B identical on both lanes (sspec prints one line per describe block):

```
bin/simple run test/01_unit/os/kernel/ipc/reply_object_spec.spl
  6 examples, 0 failures   # G1 single-use reply capability
  6 examples, 0 failures   # G2 call/reply/notification distinction
  6 examples, 0 failures   # G3 caller-death invalidation
  8 examples, 0 failures   # G4 attenuation / deny-wins on transfer
  7 examples, 0 failures   # G5 atomicity
SIMPLE_EXECUTION_MODE=interpreter bin/simple run ...  -> identical 6/6/6/8/7, 0 failures

bin/simple test test/01_unit/os/kernel/ipc/reply_object_spec.spl
  6/6/6/8/7 examples, 0 failures
  Failed: 0
  Results: 33 total, 33 passed, 0 failed        # exit 0
```

All three lanes (JIT `run`, interpreter `run`, canonical test-runner) agree:
33 examples, 0 failures.

Deliberate-red calibrations (each applied alone, then reverted; green re-verified):

| # | Breach injected | Result |
|---|-----------------|--------|
| RED-1 | one-shot never spent: `led.consume(inv_id)` -> `not led.is_consumed(inv_id)` in `reply()` Phase 4 | G1 **4 failures**, G3 **1**, G5 **1** (6 total) |
| RED-2 | deny-wins disabled: `if trial.rejected > 0` -> `> 999` | G4 **3 failures**, G5 **4** (7 total) |
| RED-3 | caller-death invalidation removed: drop `inv_valid[i] = false` and `led.consume(...)` -> `led.is_armed(...)` in `mark_task_dead()` | G3 **6 failures** (whole group) |

Post-revert re-verification: 6/6/6/8/7, 0 failures.

### Environment landmine hit during this lane

`src/os/kernel/ipc/reply_object.spl` was DELETED mid-session by a parallel
session's working-copy sync while the spec was being run. The symptom was a
misleading `semantic: Cannot resolve module: os.kernel.ipc.reply_object` that
looked like an import/resolution bug and cost a full bisect. If a brand-new
untracked `src/**` file suddenly "cannot resolve", `ls` the file FIRST.
Secondary trap: a probe of the form `use ...{X}` + `fn main(): print("ok")`
never exercises the import (unused imports are elided), so it reports a false
green — always USE the imported symbol in a resolution probe.

### §4 no-second-envelope — mechanisms REUSED, not re-implemented

- One-shot enforcement is `SingleUseLedger` from `os.kernel.ipc.cspace_spawn`
  (the Lean-proven arm/consume guard). `ReplyTable` holds TWO INSTANCES of that
  one class (`reply_ledger` for reply caps, `mint_ledger` for single-use
  transferred handles) only to keep the two id spaces disjoint. One mechanism,
  two ledgers — no second single-use mechanism was written.
- Attenuation + monotonic parent-authority checking on transferred handles
  reuses `spawn_with_cspace_tracked` verbatim (a reply transfer is expressed as a
  one-shot `SpawnSpec` recipe). No second attenuation engine.

## What is STILL BLOCKED

1. **Syscall wiring.** `_handle_ipc_send` / `_handle_ipc_recv` in
   `src/os/kernel/ipc/syscall_ipc.spl` are NOT wired to `ReplyTable`. Nothing in
   `reply_object.spl` is reachable from a live boot path, and the boot seal
   (`_seal_ambient_spawn_on_boot`) was NOT touched. Wiring is deliberately held
   until the QEMU evidence below can be produced, because a live IPC path change
   without a boot transcript is exactly the kind of unevidenced claim the ledger
   forbids.
2. **Two-process QEMU call/reply evidence.** No run slot was available in this
   lane.

## EXACT QEMU gate a future session must run

Goal: two ISOLATED user processes in one SimpleOS guest perform a blocking
`call`, the server `reply`s once with a capability handle attached, the client
observes the reply AND the received handle, and a second reply from the server is
denied by the kernel.

Preconditions (real-firmware proxy, per `.claude/rules/board-runnable.md`):
- x86_64 boot via **OVMF pflash** — never QEMU `-kernel`, never `isa-debug-exit`.
- Two distinct user binaries (`ipc_client`, `ipc_server`), each spawned into its
  OWN pledged C-Space (`spawn_with_cspace`, not `spawn_full`).

Steps:
1. Wire `ReplyTable` into `syscall_ipc.spl`:
   - `_handle_ipc_send` with a CALL flag -> `ReplyTable.call()`, block the caller
     via `BlockReason.IpcRecv`, return the `reply_id` badge to the receiver.
   - a new `_handle_ipc_reply` -> `ReplyTable.reply()`, unblock via
     `sched.unblock_task_on_cpu(caller, cpu)`.
   - `_handle_ipc_notify` -> `ReplyTable.notify()`, never blocks.
   - task teardown in the process-exit path -> `ReplyTable.mark_task_dead(tid)`.
2. Build the guest disk and boot:
   `bin/simple run src/app/test/simpleos_qemu_boot.spl --ovmf --serial-log build/ipcreply_qemu/serial.log`
   (use the OVMF pflash path already used by the `simpleos_qemu_host_gpu_2d`
   lane; do NOT introduce a `-kernel` shortcut).
3. Serial transcript MUST contain, in order and with the process ids visible:
   - `ipc: client pid=<A> call -> server pid=<B> reply_id=<R>` (A != B)
   - `ipc: client BLOCKED on reply_id=<R>`
   - `ipc: server reply reply_id=<R> transferred=1 token=<T>`
   - `ipc: client UNBLOCKED, holds token=<T> rights=READ` (rights STRICTLY
     narrower than the server's held rights — attenuation visible on the wire)
   - `ipc: server reply reply_id=<R> DENIED status=-2` (the second reply)
   - `ipc: client exit; server reply reply_id=<R2> DENIED status=-4`
     (caller-death invalidation)
4. Negative control (must also be in the transcript): a notification followed by
   a reply attempt printing `status=-3`.
5. Board leg (`.claude/rules/board-runnable.md`): the same guest image must boot
   on the KV260 rv32/rv64 path or the aarch64 board with an equivalent serial
   transcript. If the board leg is blocked, say so explicitly and file it — do
   NOT report the QEMU leg as board-runnable.

Only after steps 1-5 may the `ipc:` ledger row move off `partial`.

## Ledger

`doc/08_tracking/os/production_status.sdn` `ipc:` note updated to record the
reply-object mechanism + specs as landed, with the syscall wiring and the
two-process QEMU call/reply gate explicitly still outstanding.
