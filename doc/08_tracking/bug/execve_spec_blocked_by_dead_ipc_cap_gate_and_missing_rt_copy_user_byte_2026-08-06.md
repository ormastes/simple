# execve_spec 4/8 red: dead IPC capability gate, then a missing `rt_copy_user_byte` intrinsic

**Date:** 2026-08-06
**Status:** OPEN (root cause 2 fixed same-day by a prior commit; a follow-up ELF64
loader symbol-collision bug and a scheduler cross-call state-loss bug were
found and triaged below — see "2026-08-06 follow-up" at the bottom)
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

## 2026-08-06 follow-up: root cause 2 fixed → new ELF64 loader collision found and fixed → new scheduler state-loss gap found (deferred)

Commit `10b9ccce0166b713143ce6811d6b427db87dad13` implemented + registered
`rt_copy_user_byte`/`rt_string_from_byte_array`, taking this spec from 4/8 to
6/8. The remaining 2 failures were re-investigated end to end.

### Fixed: `byte_utils.spl`'s `read_u16_le`/`read_u32_le`/`read_u64_le` collided
### with `lib.common.compress.utilities`'s same-named, same-arg-type functions

With root cause 2 fixed, the "dispatches exec ... with valid path" test (a
**valid** synthetic ELF64 fixture) started failing with `expected -8 to equal
0` — i.e. a well-formed executable was being rejected as ENOEXEC. Root-caused
by adding a temporary debug print inside `_validate_common_header`
(`src/os/kernel/loader/elf_loader.spl`) at the `e_type != ET_EXEC` check:

```
DEBUG_ELF64 e_type=Result::Ok(2) ET_EXEC=2 e_machine=Result::Ok(62) expected_machine=62 datalen=4100
```

`e_type` printed as `Result::Ok(2)`, not `2`. `os.kernel.loader.byte_utils`
declares `fn read_u16_le(data: [u8], off: i64) -> i64` (private, no `pub`);
`src/lib/common/compress/utilities.spl` separately declares
`pub fn read_u16_le(data: [u8], pos: i64) -> Result<u16, CompressionError>`
— **identical parameter types**, differing only in name of the second param
and return type. Once `execve_spec.spl`'s large transitive import graph pulled
both modules into the same compilation, calls to `read_u16_le`/`read_u32_le`/
`read_u64_le` from `elf_loader.spl`/`elf64.spl`/`smf.spl` sometimes resolved to
the *wrong*, `Result`-returning function from the unrelated compress module
(matches the already-known `compiler_cross_module_private_symbol_collision`
class of bug — private symbols are not actually private for this resolution
step). `e_type != ET_EXEC` then compared `Result::Ok(2)` against a raw `2`,
which is never equal, so `_validate_common_header` returned
`Err("only ET_EXEC ELF64 images are supported")` for every ELF64 image,
valid or not — `build_user_process_image` therefore ENOEXEC'd unconditionally.

A smaller, real bug was fixed at the same time: `execve_spec.spl`'s
`_make_x86_64_exec()` fixture declared `p_filesz: 4` for its PT_LOAD segment
but only appended 1 byte (`0xC3`) of file-backed data, so
`byte_utils.in_range(data, 0x1000, 4)` correctly flagged the segment as
truncated (`0x1000+4=4100 > byte_len=4097`). Padded to 4 bytes
(`0xC3,0x90,0x90,0x90`) to match the declared `p_filesz`/`p_memsz`.

**Fix:** renamed the three `byte_utils.spl` functions to `lb_read_u16_le` /
`lb_read_u32_le` / `lb_read_u64_le` (unique prefix, no collision anywhere in
`src/lib/` or `src/os/`) and updated the three callers
(`elf_loader.spl`, `elf64.spl`, `smf.spl`). Verified: `elf_loader_spec.spl`
(10/10), `elf64_spec.spl` (4/4), `smf_spec.spl` (18/18) all still pass, and the
debug print showed the collision (`Result::Ok(2)`) before the rename and a
*different* failure (`-10`, see below — no longer ENOEXEC) after.

Files: `src/os/kernel/loader/byte_utils.spl`, `elf_loader.spl`, `elf64.spl`,
`smf.spl`, `test/01_unit/os/kernel/ipc/execve_spec.spl` (fixture fix only).

### Open, deferred: exec-via-`syscall_handler` can never see a task spawned in
### the same call sequence, because `Scheduler` mutations don't cross the
### plain `syscall_handler(args, scheduler, ipc, klog)` call boundary

After the ELF64 fix, "dispatches exec ..." now fails with `expected -10 to
equal 0` (`-10` = no task-control-block slot found for the exec target), and
"preserves task PID across exec" fails with
`expected Option::None to not equal nil` (`sched.get_task(TaskId(id:
pid_before))` returns `None` immediately after the spawn that supposedly
produced `pid_before`).

Root-caused with a standalone probe spec
(`sched.get_current()` before/after a syscall-13 SpawnBinary call, then
`sched.get_task(sched.get_current())`): the spawn syscall returns a nonzero
pid (proving the create succeeded *somewhere*), but the caller's own `sched`
variable never gains the new task — `get_task()` finds nothing, and
`sched.schedule()` (which would context-switch `current` to a ready task) also
finds nothing to pick, because the ready-queue enqueue from the spawn never
lands in the caller's copy of `Scheduler` either.

This matches a constraint already documented in production code, just not
previously connected to this spec's failure: `SpawnBinaryDirectState`
(`src/os/kernel/ipc/syscall_process.spl:793`) states outright:

> "Scheduler instances have value semantics across call boundaries, so the
> task created by create_user_task_pid only exists in the callee's copy.
> Callers must adopt the returned scheduler (mirrors IpcSyscallState)."

`Scheduler` is declared `pub class Scheduler:`
(`src/os/kernel/scheduler/scheduler_types.spl:606`), yet a `class` instance
passed through this codebase's cross-module call chain to
`syscall_handler(args: SyscallArgs, scheduler: Scheduler, ipc: IpcManager,
klog: KernelLog) -> SyscallResult` (`src/os/kernel/ipc/syscall.spl:309`)
behaves as if value-copied: the function returns only `SyscallResult`, never
an updated `Scheduler`, so any spawn/schedule mutation performed inside is
invisible to the caller once the call returns. `syscall_handler`'s own
docstring calls it "the legacy result-only... path used for tests and call
sites that have not yet been converted to explicit runtime-state threading" —
i.e. this is a known, intentional limitation of that specific entry point, not
a new defect. IPC syscalls (20-23) already have a state-threading replacement
(`syscall_handler_ipc_state` → `IpcSyscallState { result, scheduler, ipc }`);
process syscalls (spawn/exec/fork/wait/...) do not.

Separately (compounding, not the primary cause): a bare `Scheduler.new()`'s
`current` defaults to `TaskId(id: 0)`, but `scheduler_next_task_id_take()`
(`src/os/kernel/scheduler/scheduler_types.spl:40`) starts real task-id
allocation at **1** — so id 0 is a sentinel that is never itself a real
`TaskControlBlock`. Even with state-threading fixed, calling `syscall_handler`
for `Exec` against a fresh, never-scheduled `Scheduler` would still need a
prior `schedule()` to move `current` off the id-0 sentinel onto a real,
ready task before exec can find a valid slot to replace.

**Why deferred:** fixing this properly means adding a state-threading variant
for the process syscalls (spawn/exec/fork/wait/...) mirroring
`IpcSyscallState`/`SpawnBinaryDirectState`, and auditing every call site of
`syscall_handler` for process ids to see whether the plain entry point is
*already* silently dead code in production the same way `ipc.cap_manager` was
(root cause 1 above) — that requires the same kernel-wide, security-adjacent
scope this doc's own root cause 1 already flagged as out-of-scope for a
spec/loader-only change. Per this task's escape hatch ("stop honestly rather
than force a risky fix"), this is recorded here undone.

**What's left to do (updates the earlier list):**
1. Root cause 1 (dead `ipc.cap_manager` gate) — unchanged, still open.
2. Root cause 2 (`rt_copy_user_byte`) — **fixed**, commit
   `10b9ccce0166b713143ce6811d6b427db87dad13`.
3. ELF64 loader `read_u*_le` symbol collision — **fixed**, this update.
4. Process-syscall state threading (spawn/exec/fork/wait/... need an
   `IpcSyscallState`-style wrapper so `Scheduler` mutations survive a
   `syscall_handler` call) — **open**, newly documented here.
5. Decide whether a fresh `Scheduler.new()`'s id-0 `current` sentinel should
   itself become a real bootable task, or whether every exec-via-syscall spec
   must call `schedule()` after spawning before exec can target the spawned
   task — **open**, newly documented here.
