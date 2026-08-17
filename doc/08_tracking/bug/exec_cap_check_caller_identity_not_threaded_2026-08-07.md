# `exec_cap_check`'s scalar-caller ABI cannot carry a real `CapabilitySet` — every non-kernel caller is unconditionally denied, not "checked"

**Date:** 2026-08-07
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
proven — re-verified 2026-08-10: `bin/simple test
test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl --no-cover-check` →
`Results: 8 total, 8 passed, 0 failed`; threading a real caller identity into
it still requires the `Scheduler`/`TaskControlBlock` architecture change
described below and is out of scope for a spec-only or gate-only change)
**Severity:** Medium — not a live security hole (see "Reachability audit"
below: nothing userspace-reachable calls the affected entry points with a
nonzero caller today), but it blocks WP-21's stated goal of a genuinely
capability-gated `fs_exec_spawn` family.
**Plan:** `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`
(WP-21)

## Summary

`src/os/kernel/loader/cap_exec_gate.spl`'s `exec_cap_check(caller: i64, path:
text) -> i32` is the gate every `fs_exec_spawn_as` / `fs_exec_spawn_with_recipe`
/ `fs_exec_spawn_ring3_with_recipe` call site consults before loading
executable bytes. Before this session's fix it built a **fresh, empty**
`os.kernel.ipc.capability.CapabilityManager` per call
(`records: [TaskCapRecord]` starts `[]`), so `check()` → `_find_record` → nil
→ `false` for every kind, for every caller, always. The old header comment
said "this gate never denies today" — that was only half true: an
always-empty manager can also never ALLOW. A nonzero caller was permanently
stuck at "always denied", regardless of what it actually held, which made any
deny-only spec against it vacuous (it would pass whether or not the
capability-matching logic works at all).

## What this session fixed

Added `exec_cap_check_caps(caps: CapabilitySet, path: text) -> i32` — the real
check, built on `CapabilitySet.has(...)`, the SAME model
`TaskControlBlock.capabilities` and `src/os/kernel/loader/spawn_authority.spl`
already use in production (not the disconnected `ipc.cap_manager`/
`TaskCapRecord` store, which is a documented dead store in its own right —
see `execve_spec_blocked_by_dead_ipc_cap_gate_and_missing_rt_copy_user_byte_2026-08-06.md`).
Proven both directions in
`test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl` (8/8, sabotage-verified:
forcing the function to always return 0 turned the 4 deny cases red, reverting
restored 8/8) — a caller pledged to a `CapabilitySet` missing FileExec or
ProcessSpawn (or scoped to the wrong path prefix) is denied; a caller holding
both (or the unpledged ambient-full set) is allowed.

`exec_cap_check(caller, path)` itself is UNCHANGED in behavior: caller == 0
(kernel-origin sentinel) passes, every other caller is denied. It is now
explicit in both the code comment and this doc about WHY it can't do better.

## What's still missing: caller → `CapabilitySet` lookup

`exec_cap_check_caps` needs a real `CapabilitySet` to check. The only place
one exists for a given caller task is `TaskControlBlock.capabilities`
(`src/os/kernel/scheduler/scheduler_types.spl:92`), reachable only through a
live `Scheduler` (e.g. `scheduler.tasks[...]` or a lookup keyed by
`TaskId`). But `fs_exec_spawn_as` / `fs_exec_spawn_with_recipe` /
`fs_exec_spawn_ring3_with_recipe` (`src/os/kernel/loader/fs_exec_spawn.spl`)
take only a bare `caller: i64` scalar — no `Scheduler` or `TaskControlBlock`
handle — because `fs_exec_prepare_spawn_from_bytes` builds its OWN throwaway
bootstrap `Scheduler` internally
(`_fs_exec_new_bootstrap_scheduler()`, `fs_exec_spawn.spl:168`). This is the
exact same gap `_fs_exec_parent_caps`'s own `TODO(boot-seal)` comment already
names one line up:

> "thread the calling task's real `TaskControlBlock.capabilities` into
> `fs_exec_prepare_spawn_from_bytes`... Must land with the boot-side seeder in
> the arming session."

Closing this requires either (a) passing the live production `Scheduler`
into the fs-exec bridge instead of building a throwaway one (a real
architecture change — the bridge currently constructs a fresh 1-CPU
scheduler specifically so it doesn't need one), or (b) a separate persistent
`caller: i64 -> CapabilitySet` lookup table seeded at task-creation time,
independent of which `Scheduler` instance is in scope. Neither is safe to
improvise as a side effect of a capability-gate fix — pick one deliberately,
with its own design pass.

## Reachability audit (2026-08-07) — not a live hole today

Grepped `src/os/`, `src/app/`, and `examples/09_embedded/` for every call site
of the caller-less convenience wrappers (`fs_exec_spawn(`, `fs_exec_spawn_ring3(`)
and the caller-bearing ones invoked with a literal `0`:

- `src/os/kernel/arch/{riscv32,riscv64}/console.spl` call
  `fs_exec_spawn_with_recipe(0, SPAWN_RECIPE_CONSOLE_SHELL, path, argv, [])` —
  kernel console shell launch, trusted kernel-origin context. Legitimate.
- `src/os/kernel/loader/arm_fs_exec_spawn.spl`'s `arm_fs_exec_spawn_path` (arm64)
  calls `arm64_fs_exec_spawn(path, [], [])` — a boot/QEMU acceptance probe
  entry (`arm_fs_exec_spawn_hello_world_smf`), not userspace-reachable.
- No other production call site references the bare wrappers.

The REAL userspace-reachable syscalls that spawn/exec processes —
`_handle_exec_state` (`src/os/kernel/ipc/syscall_process.spl:307`),
`_handle_spawn_binary_state` (`:746`), `_handle_spawn_state` (:231`) — do
**not** go through `fs_exec_spawn` at all. They call `scheduler.get_current()`
(`_ambient_spawn_caller`, `:106`) for real caller identity and gate through
`spawn_authority_ambient_caps`/`_spawn_caps_for` directly. So
`Scheduler.get_current() -> TaskId` (`scheduler_lifecycle.spl:355`) IS a real,
already-used current-task-identity primitive — it's just not reachable from
inside the fs-exec bridge's own throwaway scheduler, which is the gap this
doc is about.

## Unblock condition

File tracked; unblock when either (a) or (b) above lands and
`exec_cap_check(caller, path)` is updated to build a real `CapabilitySet` for
`caller` and delegate to `exec_cap_check_caps` instead of denying outright.
