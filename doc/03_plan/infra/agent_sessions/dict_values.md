# dict-values / SimpleOS hardening lane — session notes

## Seal gate status 2026-08-01

**Decision: the boot seal stays OFF. `_seal_ambient_spawn_on_boot()` in
`src/os/kernel/boot/init_services.spl` still returns `false`.**

### What the gate is

`init_all_services()` ends with the master-plan §5.4 ambient-spawn seal:

```
spawn_authority_set_root_task(BOOT_ROOT_TASK_ID)
if _seal_ambient_spawn_on_boot():
    spawn_authority_seal_bootstrap()
```

Sealing closes the bootstrap window: after it, only the root task (`caller == 0`,
the kernel-origin sentinel) may take the ambient `spawn_full()` path in
`syscall_process.spl`. Every other caller must present a SpawnSpec recipe or is
refused `EACCES`.

### Why it is still off — the concrete blocker

`syscall_process._declared_spawn_recipe()` reads the recipe from a **process-wide
scalar** (`spawn_authority_current_recipe()`), not from the syscall arguments,
and carries this TODO in-tree:

> `TODO(boot-seal): carry the recipe id as an explicit syscall argument so a
> genuine ring-3 caller can declare it across the privilege boundary. The scalar
> only propagates for in-image callers (launcher, boot services), which is every
> migrated caller today.`

That is the blocker, and it is an ABI gap, not a flag:

- Syscall 13 (`spawn`) has **no recipe argument**. A ring-3 caller cannot set the
  scalar — it lives in kernel memory and is only written by in-image callers
  (`launcher_registry.spl:428`, `fs_exec_spawn.spl:366/392`).
- So for any genuine ring-3 spawn the declared recipe is `SPAWN_RECIPE_NONE`,
  `spawn_recipe_is_migrated(0)` is false, and the caller falls to the ambient
  path.
- With the seal armed, that ambient path returns `SPAWN_AUTHORITY_EPERM`
  for every `caller != 0`. Net effect of flipping the gate today: **every
  userland syscall-spawn (shell, WM, fs-exec launch) fails `EACCES`** while the
  in-image launcher path keeps working — i.e. an in-guest regression that only
  shows up on a real boot.

Only three recipes exist (`SPAWN_RECIPE_SHELL`, `SPAWN_RECIPE_CONSOLE_SHELL`,
`SPAWN_RECIPE_APP_LAUNCHER`, `spawn_recipes.spl:46-48`), all reachable only from
in-image callers.

### What is NOT the blocker any more

The SEALPREP lane (`78328f8e903`) recorded the arming blocker as
"`_find_source` iterates `parent.caps` while `CapabilitySet.full()` is
`caps: []`, so an ambient parent authorizes NOTHING". That specific defect is
**resolved at HEAD**: `spawn_recipe_seed_parent_caps(recipe, owner)` builds
concrete delegable tokens (`depth: 2`) and is now called on both mint paths
(`syscall_process.spl:157`, `fs_exec_spawn.spl:349`), so a migrated recipe no
longer mints deny-all. The remaining gap is purely the missing recipe argument in
the syscall ABI.

### Evidence still missing

No QEMU boot+launch transcript exists for a sealed boot. Per
`.claude/rules/board-runnable.md` the promotion bar is real-firmware boot
(OVMF pflash) plus a serial transcript showing in-guest shell/WM launch
surviving the seal. Nothing in-tree meets it.

### Promotion checklist (all four required)

1. Carry the recipe id as an explicit syscall-13 argument (removes the
   `TODO(boot-seal)` in `syscall_process._declared_spawn_recipe`).
2. Migrate the ring-3 spawn callers (shell, WM, fs-exec launch) to declare a
   recipe through that argument.
3. Flip `_seal_ambient_spawn_on_boot()` to `true` **and** update
   `test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl` — its
   "places the seal call last in boot, but leaves it BEHIND AN OFF GATE" case
   asserts the gate is off precisely so the flip cannot land silently.
4. Capture a real-firmware QEMU boot+launch serial transcript with the seal
   armed, and link it here.

### False-green fixed in the same change

`spawn_enforcement_wiring_spec.spl`'s case
*"arms the guard at the end of boot service initialization"* asserted only the
**text position** of `spawn_authority_seal_bootstrap()` inside
`init_services.spl`. The call it located sits inside `if
_seal_ambient_spawn_on_boot():`, which is `return false` — so the spec claimed an
armed guard while boot never armed one. It is now split in two:

- a source-shape case, retitled to what it actually proves, which additionally
  asserts the gate exists and reads `return false`;
- a behavioural case that runs boot's two calls through the guard's own API and
  asserts `spawn_authority_bootstrap_sealed()` and the root-allowed /
  userland-EPERM outcomes, then reopens the window so case order cannot leak
  state.
