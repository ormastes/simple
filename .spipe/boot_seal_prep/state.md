# boot_seal_prep — ambient-spawn caller migration (Phase 2 prep)

Lane: SEALPREP. Goal: do the migration work that arming
`_seal_ambient_spawn_on_boot()` depends on, WITHOUT arming it.

`src/os/kernel/boot/init_services.spl` is untouched — the seal stays gated off.

## 1. Ambient spawn caller survey (pre-edit)

| # | Caller | Entry point | Underlying path | Rights it actually needs | Status when seal armed (BEFORE migration) |
|---|--------|-------------|-----------------|--------------------------|-------------------------------------------|
| 1 | boot service start | `os.userlib.process.spawn_binary` from `src/os/kernel/boot/boot_fs.spl:397,414,431` | syscall 13 → `_handle_spawn_binary` (gate 2/3) | exec+read under `/sys/`, ProcessSpawn | OK — runs as root/pre-seal |
| 2 | app launcher | `posix_spawn_with_args` (`src/os/services/launcher/launcher_registry.spl:458,467`) → `os.kernel.process_compat` | syscall 13 → `_handle_spawn_binary` (gate 2/3) | exec+read under `/sys/apps/`, ProcessSpawn | **DENIED (EACCES)** — non-root caller |
| 3 | shell exec | `shell_exec` (`src/os/apps/shell/exec.spl:40`) → `fs_exec_spawn_ring3` | ring3 arch handoff → `fs_exec_prepare_spawn_from_bytes` | exec+read under `/bin/`,`/sys/apps/`, ProcessSpawn | **DENIED, and unauditable** — see defect D1 |
| 4 | riscv32 console shell | `fs_exec_spawn` (`src/os/kernel/arch/riscv32/console.spl:223`) | `fs_exec_spawn_as(0, ...)` | same as #3 | passes, but by **impersonating root** — defect D2 |
| 5 | riscv64 console shell | `fs_exec_spawn` (`src/os/kernel/arch/riscv64/console.spl:295`) | `fs_exec_spawn_as(0, ...)` | same as #3 | passes, by impersonating root — defect D2 |
| 6 | sshd remote exec | `x86_64_fs_exec_spawn` (`src/os/apps/sshd/sshd.spl:141`) | `x86_64_fs_exec_spawn_as(0, ...)` | exec+read under `/bin/` | passes as root — **NOT IN SCOPE** (owned by another lane) |
| 7 | raw entry spawn syscall | `_handle_spawn` (`syscall_process.spl:167`) | gate 1/3, already routed | ambient (boot/init compat) | DENIED for non-root — intended |
| 8 | x86_64 direct spawn | `dispatch_spawn_binary_direct_state` → `_spawn_from_resolved_bytes_for_arch_state` (`syscall_process.spl:769`) | gate 3/3, already routed | per-image | DENIED for non-root — needs recipe |
| — | window manager | `src/os/services/wm/**` | — | — | **WM does not spawn processes.** `wm_world.spl:128 self.base.spawn()` is an ECS *entity* spawn; `wm_notify_app_launched` only records a pid the launcher produced. WM needs no recipe. |

Already-routed ambient sites (unchanged by this lane): `syscall_process.spl`
gates 1/3 (`_handle_spawn`), 2/3 (`_handle_spawn_binary`), 3/3
(`_spawn_from_resolved_bytes_for_arch_state`), plus
`fs_exec_spawn.spl:262`.

### Defects found during the survey

- **D1 — ring3 spawn never records its caller.** `fs_exec_spawn_ring3`
  (`fs_exec_spawn.spl:287`) goes straight to `_fs_exec_spawn_ring3_active`
  without calling `spawn_authority_note_caller`, so
  `fs_exec_prepare_spawn_from_bytes` reads a **stale** `g_spawn_current_caller`
  scalar. The audit line then names the wrong task. Fixed in this lane by
  giving the ring3 entry a caller+recipe-recording variant.
- **D2 — console-launched programs inherit `spawn_full()`.** `fs_exec_spawn`
  calls `fs_exec_spawn_as(0, ...)`, the kernel-origin/root sentinel. The console
  legitimately IS kernel-context, so the caller id is honest — but its CHILD, an
  arbitrary user program named on a `launch` line, was handed the full ambient
  set and the seal could never observe it. Fixed by routing the consoles through
  `SPAWN_RECIPE_CONSOLE_SHELL`, which mints the child FileExec+FileRead under
  `/bin/` plus ProcessSpawn instead. The caller id stays 0.
- **D3 (BLOCKER for arming, discovered here) — an ambient `full()` parent
  authorizes NOTHING under a SpawnSpec.** `cspace_spawn._find_source` iterates
  `parent.caps`, and `CapabilitySet.full()` is `caps: [], is_pledged: false` —
  zero concrete tokens. So minting a recipe pouch from a task that only holds
  ambient authority yields a **deny-all** child (every grant `rejected`).
  Migration therefore needs a *root-grant seeding* step: each migrated service
  task must hold concrete, delegable tokens before the seal is armed. Provided
  here as `spawn_recipe_seed_parent_caps()`; wiring it into the boot path is
  part of the arming session, not this lane.

## 2. What this lane changed

- `src/os/kernel/loader/spawn_recipes.spl` (new) — the recipe table. One
  `SpawnSpec` per legitimate userland spawn caller, least-authority grants
  only, plus the root-grant seeder that makes D3 tractable.
- `src/os/kernel/loader/spawn_authority.spl` — recipe-aware gate
  (`spawn_authority_check_spawn`, `spawn_authority_spawn_caps`) layered on the
  SAME ambient guard; recipe scalar propagation mirroring the existing caller
  propagation. No second spawn path: recipe spawns still descend through
  `fs_exec_prepare_spawn_from_bytes` / `create_user_task_pid`.
- `src/os/kernel/loader/fs_exec_spawn.spl` — `fs_exec_spawn_with_recipe` and
  `fs_exec_spawn_ring3_with_recipe`; the prepare bridge now asks
  `spawn_authority_spawn_caps` instead of `spawn_authority_ambient_caps`
  (identity-equal on the ambient path).
- `src/os/apps/shell/exec.spl` — `shell_exec_as(caller, ...)` uses
  `SPAWN_RECIPE_SHELL`; `shell_exec` keeps its signature and delegates.
- `src/os/kernel/arch/riscv32/console.spl`, `.../riscv64/console.spl` — console
  shells use `SPAWN_RECIPE_CONSOLE_SHELL` with their real caller id.
- `src/os/services/launcher/launcher_registry.spl` — the app-launch spawn
  declares `SPAWN_RECIPE_APP_LAUNCHER` before descending into
  `posix_spawn_with_args`.
- `src/os/kernel/ipc/syscall_process.spl` — the 3 existing gates consult the
  recipe-aware check, so a migrated caller is admitted after sealing while a
  bare ambient non-root spawn is still EACCES.

## 3. Proof that arming would be safe (without arming)

`test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl` forces the
sealed behaviour locally (`spawn_authority_seal_bootstrap()` + a non-root
caller) and asserts, per migrated caller, that the recipe path is admitted and
mints a non-empty attenuated pouch, while the same caller on the bare ambient
path is denied. The global boot seal is never touched.

### Verdicts (A/B, both engines)

Default engine (log `build/sealprep_spec.log`), one line per describe block:

```
boot-seal readiness: migrated callers survive the seal        4 examples, 0 failures
boot-seal readiness: the minted pouch is real and attenuated  4 examples, 0 failures
boot-seal readiness: the seeding precondition is load-bearing 2 examples, 0 failures
boot-seal readiness: recipes request least authority          3 examples, 0 failures
boot-seal readiness: recipe propagation is scoped, not sticky 1 example,  0 failures
Results: 14 total, 14 passed, 0 failed
```

Interpreter (`bin/simple test --interpret ...`, log
`build/sealprep_spec_interp.log`): `Results: 14 total, 14 passed, 0 failed`,
identical per-block counts. No engine divergence.

Regression on the pre-existing gate `spawn_authority_contract_spec.spl` (log
`build/sealprep_contract.log`): `Results: 16 total, 16 passed, 0 failed`
(5 / 6 / 5 per block) — the ambient guard is unchanged for existing callers.

Serial audit trace captured during the run — this is the behaviour the QEMU
transcript must reproduce on real firmware:

```
[spawn-auth] bootstrap sealed root=0
[spawn-auth] deny ambient spawn caller=4242                     <- unmigrated, sealed
[spawn-auth] recipe spawn caller=4242 recipe=shell         rejected=0
[spawn-auth] recipe spawn caller=4242 recipe=console-shell rejected=0
[spawn-auth] recipe spawn caller=4242 recipe=app-launcher  rejected=0
[spawn-auth] recipe spawn caller=4242 recipe=shell         rejected=3  <- ambient full() parent (D3)
```

**Binary-identity caveat.** The deployed `bin/simple` is currently the Rust
bootstrap SEED (`readlink -f` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
which prints the seed warning banner). That is pre-existing environment state,
not something this lane introduced, but these verdicts are therefore SEED
verdicts. Re-run on the self-hosted binary in the arming session before treating
them as the production gate.

## 4. RESUME COMMAND for the arming session

```bash
# 1. Re-run the readiness proof (must be green before touching the flag):
bin/simple test test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl
bin/simple test test/01_unit/os/kernel/loader/spawn_authority_spec.spl

# 2. Wire the D3 seeder into boot (REQUIRED — without it every migrated
#    caller mints a deny-all pouch because ambient full() has no tokens):
#      in src/os/kernel/boot/init_services.spl, before sealing, call
#      spawn_recipe_seed_parent_caps(SPAWN_RECIPE_*, <task owner>) for the
#      shell / console / launcher service tasks and install the result as
#      each task's TaskControlBlock.capabilities.

# 3. ONE-LINE FLIP (do NOT do this before step 2 is green):
#      src/os/kernel/boot/init_services.spl :: _seal_ambient_spawn_on_boot()
#      -> true

# 4. Evidence run — real-firmware QEMU boot + launch transcript
#    (OVMF pflash, never -kernel / isa-debug-exit):
sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke   # harness sanity
#    then the SimpleOS x86_64 OVMF boot; capture serial showing
#      [spawn-auth] bootstrap sealed root=...
#      [spawn-auth] recipe spawn caller=<non-root> recipe=<id>
#      a successful shell/launcher launch AFTER the seal line
#      at least one "[spawn-auth] deny ambient spawn caller=" for an
#      unmigrated ambient attempt

# 5. Ledger: flip production_status.sdn capability_spawn: to "armed" only
#    once the transcript in step 4 exists.
```

## 5. Explicitly NOT done here

- The flag is still `false`. `init_services.spl` untouched.
- The D3 seeder is written and unit-proven but NOT wired into boot — that is a
  boot-path edit in a file this lane does not own.
- No QEMU boot transcript (no run slot). Arming without one would EACCES
  userland spawns with nothing to observe; that call stands.
