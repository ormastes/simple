# Lane P2 — Process/Loader hardening (SimpleOS production harden)

Updated: 2026-07-27. Uncommitted (working copy only, per lane instructions).

Plan: `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` (lane P2).
Research: `doc/01_research/domain/simpleos_production_host_master_plan.md` §5.2–5.4.

## Goal (this increment)

Master plan §5.4 "Remove ambient spawn authority": make `spawn_full()` legal
only for the root task during bootstrap, keep SpawnSpec the sanctioned path, and
prove the effective-rights intersection formula:

```
effective_rights = parent_delegable & executable_policy_ceiling
                 & system_policy_ceiling & manifest_request − explicit_denials
```

Bounded to loader/lifecycle-owned files. `src/os/kernel/ipc/**` (SpawnSpec,
`spawn_full`) is READ-ONLY for this lane (P1 owns it) and was not modified.

## Changes

| File | Change |
|---|---|
| `src/os/kernel/loader/spawn_authority.spl` | **NEW.** The guard. Scalar-module-var phase model (`g_spawn_bootstrap_sealed`, `g_spawn_root_task`, `g_spawn_current_caller`, `g_spawn_ambient_denials`), guard fns, accessor fns, and the pure effective-rights helpers. |
| `src/os/kernel/loader/fs_exec_spawn.spl` | Dropped the direct `use ... cspace_spawn.{spawn_full}` import. `fs_exec_prepare_spawn_from_bytes` now installs `spawn_authority_ambient_caps(spawn_authority_current_caller())` instead of `spawn_full()`. `fs_exec_spawn_as` records/clears the caller around the descent. |
| `test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl` | **NEW.** Contract spec (11 examples). |

### Guard semantics

- `g_spawn_bootstrap_sealed == false` (the .bss-zero default, therefore also the
  correct fail-safe state when a freestanding module initializer never runs) =
  bootstrap window OPEN → ambient spawn allowed, boot path unchanged.
- `spawn_authority_seal_bootstrap()` closes the window. After that only
  `caller == g_spawn_root_task` (default 0 = the existing kernel-origin sentinel
  used by `cap_exec_gate.exec_cap_check`) keeps ambient authority.
- A denied caller gets `SPAWN_AUTHORITY_EPERM (-1)` from
  `spawn_authority_check_ambient`, and `spawn_authority_ambient_caps` returns
  `CapabilitySet.empty()` — the PLEDGED deny-all set, so an unauthorized ambient
  spawn produces a powerless task rather than a god-mode one (fail closed).
- Pure helpers: `spawn_effective_rights`, `spawn_rights_without` (denial
  subtraction via `base ^ (base & denials)` — no bitwise-not width assumption),
  `spawn_rights_is_subset`, `spawn_spec_requested_rights` (a zero
  `AttenuationSpec.rights_mask` means "inherit parent", never "all rights"), and
  `spawn_spec_effective_rights`.

### Freestanding discipline honoured

Plain `fn`s + scalar module vars only. No module-level array/`[text]`
initializers, no class construction, no trait-object dispatch on the ring-0
path — per the `fs_exec_resolve.spl` header rules.

### Why the caller is a scalar, not a parameter

`fs_exec_prepare_spawn_from_bytes` is the shared cross-arch bridge consumed by
`x86_64_fs_exec_spawn.spl`, `arm64_fs_exec_spawn.spl`,
`riscv64_fs_exec_spawn.spl` and `arm_fs_exec_spawn.spl`. Threading a `caller`
param through all of them is a multi-file signature change and was out of scope
for one increment; the gated entry (`fs_exec_spawn_as`) records the caller into
a scalar before descending and clears it after. Boot paths that never set it
read 0 = root, preserving boot. **Follow-up:** promote it to a real parameter
once the per-arch entries are touched anyway (see resume plan step 3).

## Spec verdict

Recipe: `/tmp/p2lane/bin/p2job` = `bin/release/x86_64-unknown-linux-gnu/simple`.

```
timeout 300 /tmp/p2lane/bin/p2job run \
  test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl
```

- `spawn authority contract (master plan 5.4)` → **5 examples, 0 failures**
- `effective rights are an intersection (no amplification)` → **6 examples, 0 failures**

Deliberate-red calibration: replacing the guard condition in
`spawn_authority_ambient_caps` with `if false:` turned
`✗ denies post-bootstrap ambient spawn for a non-root caller` red
(`5 examples, 1 failure`); restored, back to green. The spec can fail.

Regression check on neighbouring loader specs (same binary, before vs. after the
`fs_exec_spawn.spl` edit — identical results, so no regression introduced):

| Spec | Result | Note |
|---|---|---|
| `exec_from_fs_spec.spl` | 16 examples, 0 failures | green |
| `spawn_pipeline_spec.spl` | 4+2 failures across 5 describes | **pre-existing** (identical at baseline; `crc32_calculate` HIR lowering error) |
| `x86_64_fs_exec_spawn_spec.spl` | 3 examples, 1 failure | **pre-existing** (identical at baseline) |

### Lint status (recorded, not normalized)

`bin/simple lint src/os/kernel/loader/spawn_authority.spl` → 13 errors, ALL
`primitive_api` ("public API parameter/return uses bare primitive type
`i64`/`u32`"). This is the established ring-0 pattern, not a new deviation: the
pre-existing sibling gate `cap_exec_gate.spl` fails the identical lint (2
errors) for `exec_cap_check(caller: i64, path: text) -> i32`, and
`fs_exec_spawn.spl:291` (`fs_exec_spawn_as`) already failed it before this
change. Satisfying `primitive_api` here means newtype wrappers, i.e. struct
construction on the freestanding ring-0 path — which the discipline in
`fs_exec_resolve.spl` explicitly forbids. Recording the conflict rather than
silently accepting a workaround: **the rule and the freestanding constraint are
in genuine tension for `src/os/kernel/**`, and `primitive_api` probably needs a
scoped exemption for ring-0 modules.** Worth filing separately.

The two additional `fs_exec_spawn.spl` lint errors (`COLL006` string concat in
loop, line 161) are pre-existing and untouched by this change.

## Remaining ambient-spawn sites (4)

None remain under `src/os/kernel/loader/**` or `src/os/kernel/lifecycle/**`
(`lifecycle/task_cleanup.spl` has no spawn/capability path at all). Every
remaining site is outside this lane's exclusive paths.

| # | Site | Enclosing fn | Owner | Notes |
|---|---|---|---|---|
| 1 | `src/os/kernel/ipc/syscall_process.spl:143` | `_handle_spawn` | P1 (IPC) | The live `sys_spawn` syscall — highest-value target; a user task reaching this today still gets `spawn_full()`. |
| 2 | `src/os/kernel/ipc/syscall_process.spl:660` | `_handle_spawn_binary` | P1 (IPC) | Binary-blob spawn path. |
| 3 | `src/os/kernel/ipc/syscall_process.spl:729` | `_spawn_from_resolved_bytes_for_arch_state` | P1 (IPC) | Arch-state spawn path. |
| 4 | boot path — **no caller of `spawn_authority_seal_bootstrap()` exists yet** | — | boot/init owner (outside P2 paths) | Until something seals the window, the guard is permanently permissive; the mechanism is in place and spec-proven, but not yet ARMED in a live boot. This is the single most important follow-up. |

`CapabilitySet.full()` has exactly one live call site remaining repo-wide
(`cspace_spawn.spawn_full` itself, line 351) — the regression guard in that
docstring still holds.

## Resume plan

1. **Arm the guard.** Find the boot/init sequence point right after init is
   started (`src/os/kernel/boot/**` or the per-arch kernel entry) and call
   `spawn_authority_set_root_task(<init pid>)` then
   `spawn_authority_seal_bootstrap()`. Needs a cross-lane note to the boot owner
   — it is not a P2 path. Gate: a QEMU boot where a post-init non-root
   `fs_exec_spawn_as` logs `[spawn-auth] deny ambient spawn caller=N`.
2. **Hand sites 1–3 to P1** (or take them after P1 lands) by replacing
   `spawn_full()` with `spawn_authority_ambient_caps(caller)` — the syscall
   handlers already have the calling task id in `SyscallArgs`, so no scalar
   propagation is needed there; they can call the guard directly.
3. **Promote the caller scalar to a parameter** on
   `fs_exec_prepare_spawn_from_bytes` / `fs_exec_prepare_spawn`, updating the
   four per-arch entries in the same change; then delete
   `spawn_authority_note_caller` / `_current_caller` / `_clear_caller`.
   (Deletion condition for the scalar-propagation shim.)
4. **Wire real SpawnSpec rights.** `spawn_spec_effective_rights` is currently a
   pure helper with no live consumer; connect it once P8's LLM security-profile
   registry lands (it supplies `system_policy_ceiling` + `explicit_denials`) and
   once §5.3's `SimpleArtifactManifest` supplies
   `executable_policy_ceiling` + `manifest_request`.
5. **Remaining lane-P2 tranche items not started:** global job/process manager
   (§24.4/5), live child CSpace install, descriptor-based ELF exec (§24.7/8),
   and the reap path in `lifecycle/`.

## Blockers

- Guard is not ARMED in a live boot (site 4) — mechanism + spec only. Not a
  QEMU/board claim; no boot evidence is asserted by this increment.
- Sites 1–3 are in P1's exclusive path; cannot be fixed from this lane.
- `spawn_pipeline_spec.spl` and `x86_64_fs_exec_spawn_spec.spl` carry
  pre-existing failures on main (verified at baseline, not caused here).
