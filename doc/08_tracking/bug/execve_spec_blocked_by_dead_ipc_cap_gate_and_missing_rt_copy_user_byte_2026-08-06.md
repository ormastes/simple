# execve_spec 4/8 red: dead IPC capability gate, then a missing `rt_copy_user_byte` intrinsic

**Date:** 2026-08-06
**Status:** OPEN (spec partially repaired; two production gaps documented, not fixed)
**Severity:** High (the capability gate makes several syscalls dead code on the
`syscall_handler` path; the missing intrinsic blocks any spec/test from
exercising `_handle_exec`'s user-pointer copy logic at all)

## Symptom

`test/01_unit/os/kernel/ipc/execve_spec.spl` had 4 of 8 examples red:

- `expected -1 to equal 0` (exec dispatch success case)
- `expected -1 to equal -2` (ENOENT case)
- `expected -1 to equal -8` (ENOEXEC case)
- `expected Option::None to not equal nil` (PID preservation)

All four look independent (four different assertions, four different `it`
blocks) but trace to **one proximate cause**, and fixing that proximate cause
exposes a **second, separate** blocking gap. Neither gap is safe to fix inside
a spec-only change.

## Root cause 1 (now worked around in the spec): `ipc.cap_manager` records are
## never granted in production, so `_cap_check`-gated syscalls are dead code

`src/os/kernel/ipc/syscall.spl` gates several syscalls on
`_cap_check(ipc, caller, <kind>)`, which delegates to
`ipc.cap_manager.check(task, kind)` (`src/os/kernel/ipc/capability.spl:88`).
That function does:

```
fn check(task: TaskId, required: CapabilityKind) -> bool:
    val record = self._find_record(task)
    if record == nil:
        return false
    ...
```

`_find_record` walks `self.records: [TaskCapRecord]`, populated only by
`CapabilityManager.init_task_record()` / `.init_task()` / `.cap_grant()`.
**Grepped across the whole non-test tree, `init_task_record` and `.init_task`
have zero callers outside `capability.spl` itself and test specs.** Confirmed
empirically: a debug print at `syscall.spl` case 13 showed
`DEBUG case13 cap_check=false caller=0` for a caller task with no prior grant.

This means every syscall gated this way — Spawn (2), SpawnBinary (13),
EnterUserBlocking (14), Fork (57), Exec (59), DlOpen (65) — unconditionally
returns `SYSCALL_EPERM` (-1) for **any** caller that reaches it through
`syscall_handler`, because no code path ever seeds a capability record for a
newly created task in that manager.

**This is dead code today, not a live outage**, because production process
creation does not go through this gate at all: boot/fs-exec spawns processes
via `src/os/kernel/loader/fs_exec_spawn.spl`'s `spawn_full()` /
`sched.create_task()` direct path, which never references `IpcManager` or
`cap_manager`. The newer `spawn_authority`/CSpace capability system
(`spawn_authority.spl`, `spawn_recipes.spl`) is what actually gates real
spawns; the `ipc.cap_manager`-based gate in `syscall.spl` is a second,
disconnected capability system that nothing wires grants into. If any real
ring-3 process ever issues these six syscalls through the trap/syscall_handler
path, they will always get EPERM.

**Spec-level workaround applied:** `execve_spec.spl` now has a
`_capable_ipc_for(task: TaskId) -> IpcManager` helper that seeds
`ipc.cap_manager.init_task_record(task, true)` before use, and each test
reuses one `IpcManager` instance across its spawn+exec syscall sequence
(mirroring the persistent `g_trap_ipc`/`g_shim_ipc` production pattern —
the original spec passed a **fresh** `IpcManager.new()` to every
`syscall_handler()` call, which independently would have discarded any grant
even if one existed). This makes the spec exercise `_handle_exec`'s own
logic instead of being blanket-denied before it runs.

**Not fixed:** the production wiring gap itself. A real fix needs either (a)
wiring `_handle_spawn`/`_handle_spawn_binary`/`_handle_fork` to call
`ipc.cap_manager.init_task_record()` for the new task (and something to seed
the *very first* boot task, since it must already hold `ProcessSpawn` before
issuing syscall 13/2), or (b) deleting/replacing the `ipc.cap_manager` gate on
these six syscalls in favor of the `spawn_authority` system that actually
governs real spawns today. Both are security-relevant, kernel-wide changes
outside the scope of a spec fix — deferred here.

## Root cause 2 (blocks all three exec-body tests even after root cause 1 is
## worked around): `rt_copy_user_byte` has no interpreter implementation

Once the capability gate stopped masking `_handle_exec`, all three tests that
reach `_handle_exec`'s body (dispatch-success, ENOENT, ENOEXEC, PID
preservation) now fail with:

```
semantic: unknown extern function: rt_copy_user_byte
```

`_handle_exec` calls `_copy_user_bytes()` (`syscall_process.spl:577`), which
loops calling `rt_copy_user_byte(ptr_addr + i)` — declared
`extern fn rt_copy_user_byte(ptr_addr: u64) -> u8` in four `.spl` files
(`syscall_process.spl:43`, `syscall_spm.spl:26`, `syscall_file.spl:23`,
`x86_64_fs_exec_spawn.spl:205`, `sosix/process.spl:7`). Declaring the extern
does **not** register a callable native/interpreter symbol by itself in this
codebase — the interpreter has a separate registry
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, `insert_simple!`
macro calls) that maps extern names to Rust implementations
(`src/compiler_rust/compiler/src/interpreter_extern/memory.rs`).

Confirmed by exhaustive grep: **`copy_user` does not appear anywhere in
`src/compiler_rust/` — no registry entry, no Rust function.** Compare the
sibling `rt_ptr_write_i64`/`rt_ptr_read_i64`/`rt_ptr_write_u8` family, which
all exist in `memory.rs` and are registered — but there is no `rt_ptr_read_u8`
or `rt_copy_user_byte` counterpart. This looks like a straightforward missing
byte-read primitive (structurally like `rt_ptr_write_u8` in reverse), not a
novel design problem — but implementing and registering a new native
interpreter intrinsic requires touching the Rust seed
(`src/compiler_rust/compiler/src/interpreter_extern/memory.rs` +
`mod.rs`) and a bootstrap rebuild to deploy it, which this repo's own rules
flag as non-default ("Fix .spl not Rust", "No bootstrap unless essential") and
which is well outside the scope of a spec fix.

## Why this is deferred rather than force-fixed

Both gaps are genuine and both are outside safe scope for a spec-only change:
root cause 1 touches kernel capability-security wiring shared by six syscalls;
root cause 2 requires a new Rust interpreter intrinsic + bootstrap rebuild.
Per this task's own escape hatch ("if deeper/riskier than expected, stop and
document precisely rather than force a risky fix"), both are recorded here
instead of patched. **All four originally-reported failures share these same
two causes** — there is no independent subset of the four that can be fixed
without touching one or both gaps, so nothing was force-fixed to get a partial
green count.

## What's left to do

1. Decide root cause 1's real fix (wire `init_task_record` into spawn, or
   retire the dead `ipc.cap_manager` gate in favor of `spawn_authority`).
2. Implement + register `rt_copy_user_byte` (or an equivalent byte-read
   primitive `_copy_user_bytes` can call) in the interpreter, then rebuild.
3. Re-run `execve_spec.spl`; expect it to reach real assertions past
   `expect(exec_result.value).to_equal(0)` in the PID-preservation test for
   the first time — those (`task.is_user`, `task.id.id == pid_before`) have
   never executed and are unproven.
4. Check `test/01_unit/os/kernel/ipc/syscall_spec.spl`, which uses the same
   `IpcManager.new()`-per-call pattern with `id: 13` calls — likely red for
   the same root cause 1, additional evidence this is systemic, not
   execve-specific.
5. `test/unit/os/kernel/ipc/execve_spec.spl` and `.spipe_matchers_*` variants
   of these specs exist alongside the `01_unit` copies — check which are live
   before any future fix lands, so a fix doesn't get applied to one copy and
   leave a duplicate red.

## Evidence trail

- `DEBUG case13 cap_check=false caller=0` — direct proof of root cause 1,
  captured via a temporary debug print in `syscall.spl` case 13 (reverted,
  not committed).
- `semantic: unknown extern function: rt_copy_user_byte` — reproduced with
  the extern explicitly declared in the spec file, ruling out a spec-side
  declaration gap; confirmed by the empty `copy_user` grep across
  `src/compiler_rust/`.
