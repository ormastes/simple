# Lane INT-1 — spawn-authority ENFORCEMENT wiring

Status: **DONE (host-spec verified; no QEMU boot evidence)** — 2026-07-27
Scope: arm the previously UNARMED `src/os/kernel/loader/spawn_authority.spl`
guard at boot, and route the three ambient `spawn_full()` sites through it.

## What changed

| File | Change |
|---|---|
| `src/os/kernel/boot/init_services.spl` | boot seal: `BOOT_ROOT_TASK_ID` const + Step 6 seal at end of `init_all_services()`; `services_spawn_authority_sealed()` accessor |
| `src/os/kernel/ipc/syscall_process.spl` | `_ambient_spawn_caller` / `_ambient_spawn_denied` helpers + 3 guarded call sites; direct `spawn_full` import dropped |
| `test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl` | new — state machine + wiring spec |

Not touched (other lanes' paths): `spawn_authority.spl`, `cspace_spawn.spl`.

## Boot-seal call site

`src/os/kernel/boot/init_services.spl` `init_all_services()`, new **Step 6**,
after storage / PCI dump / network / display / VFS-ready and *before* the final
summary block:

- L125 `spawn_authority_set_root_task(BOOT_ROOT_TASK_ID)`
- L126 `spawn_authority_seal_bootstrap()`

`BOOT_ROOT_TASK_ID = 0`. **Verified against the guard source**: there is no
kernel-wide `INIT_TASK`/`ROOT_TASK` constant (grepped `src/os/kernel/**` for
`INIT_TASK|ROOT_TASK|init_task_id|root_task|INIT_PID|ROOT_PID` — zero hits
outside `spawn_authority.spl`). Both `spawn_authority.spl` (header L39) and
`cap_exec_gate.spl` use `caller == 0` as the kernel-origin/root sentinel, and
`spawn_authority.spl` defaults `g_spawn_root_task = 0` in zeroed `.bss`, so 0 is
the correct root identity. `Scheduler.get_current()` also reports `TaskId(id: 0)`
while no user task is current, so the kernel's own boot-path spawns stay allowed.

## Sites guarded: 3 of 3 (none deferred)

Caller id is obtained from `Scheduler.get_current().id.to_i64()` — the same
source `_handle_getpid` uses, so it is exactly the pid the caller sees. **No
caller id was fabricated at any site.**

| # | Site | Line (post-edit) | Denial return |
|---|---|---|---|
| 1 | `_handle_spawn` | L181-184 | `SyscallResult(value: 0 - EACCES as i64)` |
| 2 | `_handle_spawn_binary` | L702-705 | `SyscallResult(value: 0 - EACCES as i64)` |
| 3 | `_spawn_from_resolved_bytes_for_arch_state` | L775-778 | `SpawnBinaryDirectState(pid: 0 - EACCES as i64, scheduler: scheduler)` |

Shape at every site:

1. `val caller = _ambient_spawn_caller(scheduler)`
2. `if _ambient_spawn_denied(caller): return <permission-denied>`
3. `val caps = spawn_authority_ambient_caps(caller)` (was `spawn_full()`)

`_ambient_spawn_denied` calls `spawn_authority_check_ambient`, re-checks
`spawn_authority_bootstrap_sealed()` so the fail-open boot window is explicit at
the call site, and on the refusal path takes+drops
`spawn_authority_ambient_caps(caller)` so the guard's audit counter
(`spawn_authority_denial_count()`) actually moves for kernel refusals.

`spawn_full` is no longer imported by `syscall_process.spl`; the only remaining
ambient grant flows through `spawn_authority_ambient_caps()`, which returns
`spawn_full()` for authorized callers and `CapabilitySet.empty()` (pledged
deny-all) otherwise. `EACCES` (13) was chosen over `EPERM` because it is already
the file's established permission-denial errno (`_process_grant_errno_for_path`).

### Freestanding discipline
Plain `fn`s over scalars only — no module-level array/`[text]` initializers, no
class construction, no trait-object dispatch. The gate adds at most **one** extra
stack frame in front of an already-deep spawn chain (`_ambient_spawn_caller` and
`_ambient_spawn_denied` are leaf-ish; `get_current()` is a single field read,
`self.current`).

## Spec verdict

`test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl`

```
6 examples, 0 failures
```

Binary: `/tmp/int1/bin/int1job` (copy of `bin/release/x86_64-unknown-linux-gnu/simple`);
`timeout 300 /tmp/int1/bin/int1job run <spec>` from repo root.

Cases: open window admits everyone (ambient set not pledged) / sealed window
denies non-root with exactly `-1` == `SPAWN_AUTHORITY_EPERM` and hands back the
pledged deny-all set while root stays allowed / denial counter moves by exactly
0 on allow and exactly 1 per refusal / reopen readmits and freezes the counter /
all three syscall sites are wired (occurrence counts asserted as absolute 3, and
`val caps = spawn_full()` asserted absent) / boot arms the guard with root set
before seal, after storage+display init.

**Falsification proven:** commenting out `spawn_authority_seal_bootstrap()` in
`init_services.spl` produced `6 examples, 1 failure`
(`expected -1 to be greater than 4985`); source restored and re-verified green.

Lint: `int1job lint` on all three files — `Lint passed: all files clean`.

**No regression:** `test/01_unit/os/kernel/ipc/syscall_spec.spl` reports
`47 examples, 46 failures` **both** with my changes and with the pristine
`HEAD` copies of the two source files restored (A/B run via `git show HEAD:...`).
Those 46 failures are pre-existing (`semantic: invalid assignment: cannot index
assign value of type array`) and unrelated to this lane.
`test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl` (the pre-existing
guard contract): `6 examples, 0 failures`.

## Blockers / risks

1. **NO QEMU OR BOARD BOOT EVIDENCE THIS INCREMENT.** Everything above is
   host-spec evidence. The seal has never been exercised in a real boot.
2. **Behavioural change with real blast radius (read this first).** Before this
   lane, ambient spawn was unconditional. After it, once `init_all_services()`
   completes, **every syscall-initiated spawn from a userland task (pid != 0) is
   refused EACCES** — that is exactly master plan 5.4's intent, but it means any
   in-guest flow that spawns via syscall 13 (shell launching apps, WM launching
   apps, fs-exec) will fail until those callers move to a SpawnSpec recipe
   (`cspace_spawn.spawn_with_cspace`) or are otherwise granted root identity.
   This lane could not test that path. **One-line disarm if a boot gate regresses:
   delete the `spawn_authority_seal_bootstrap()` call at
   `init_services.spl:126`** (leaving `set_root_task` in place is harmless).
3. **Follow-up needed (not this lane):** the SpawnSpec migration for the userland
   spawn callers, so the seal is safe to keep armed. Until then, treat item 2 as
   the gating question for any boot gate that exercises in-guest launch.
4. `init_all_services()` has no other exit path, so the seal is unconditional
   once boot service init is reached — if a future early-return is added there,
   the seal must move with it or the window silently stays open.
