# Lane ECS3 — two-hop mutation sweep of the remaining SimpleOS service worlds

**Date:** 2026-07-27
**Team:** CONVERGE
**Status:** COMPLETE (not committed — lane was told not to commit or push)
**Binary used for every verdict:** `build/native_probe/simple`
**Bug:** `doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md`
(see the "Swept 2026-07-27 (lane ECS3 ...)" section for the full ledger)

## Scope executed
The ECS2 handoff list, verbatim: `src/os/services/{ds,devfs,pipefs,clock,procfs,
sched,rs,pm}_service.spl`, `devfs_filesystem.spl`, `procfs_filesystem.spl`,
`wm/wm_world.spl`, `wm/wm_service.spl`, `fs_apps/app_loader_world.spl`,
`src/os/apps/{calculator,clock,hello_world}/**`.

Not touched (owned by other live lanes): `services/container/**`,
`services/tty_service.spl`, `services/service_manifest.spl`, `services/vfs/**`,
`kernel/fs/**`, `compiler/**`, `build/board_check/**`.

## Source files changed
- `src/os/services/ds_service.spl` (salvaged from the interrupted run, completed
  + `ds_notify_count_value()` accessor)
- `src/os/services/devfs_service.spl`
- `src/os/services/pipefs_service.spl`
- `src/os/services/procfs_service.spl`
- `src/os/services/rs_service.spl`
- `src/os/services/clock_service.spl`
- `src/os/services/sched_service.spl`
- `src/os/services/pm_service.spl`
- `src/os/services/wm/wm_service.spl`

## Spec files changed / added
- `test/01_unit/os/services/{ds,devfs,pipefs,procfs,rs,clock,sched}_service_spec.spl`
- `test/01_unit/os/services/pm_service/pm_service_spec.spl`
- `test/01_unit/os/services/wm/wm_world_multi_window_identity_spec.spl` (NEW)

## Verdicts (every summary line per describe block)
ds 19/0, devfs 15/0, pipefs 19/0, procfs 13/0, rs 21/0, clock 15/0, sched 12/0,
wm_world 5/0. pm_service: new regression block 3/0; file still carries 3
pre-existing failures of an unrelated class (down from 8 at HEAD).

## What the next lane must know
1. **`Entity(id: 0)` as a not-found sentinel is a landmine.** Fixed in
   `sched_service.find_entity_for_task`; grep the rest of the tree for
   `e.id == 0` / `Entity(id: 0` used as "missing".
2. **A struct world passed by value into a free-function ECS system silently
   discards all its writes.** Found in `clock_service.sys_fire_due_alarms` and
   both `sched_service` systems; all three now return the world. Any other
   `fn sys_*(world: XWorld)` has the same defect.
3. **Dangling `extern fn` with no implementation** aborts at runtime the moment
   the code path becomes reachable. Two found (`clock_notify`,
   `sched_mechanism_set_priority`), both converted to module stubs. Both were
   only reachable *after* the identity fix.
4. **`expect(e.id).to_be_greater_than(0)` on a fresh world is always wrong** —
   `EntityAllocator` allocates id 0 first. Six specs carried it. Grep for it.
5. **Cross-import reads of a mutable module-level `var` observe the initial
   value** — always export a `*_count_value()` accessor instead.
6. **Open, handed on:** `pm_service.spl`'s `extern fn signal_deliver` /
   `loader_exec` declarations shadow both the real implementations
   (`os/posix/signal_compat.spl:171`, `os/kernel/loader/loader_api.spl:159`) and
   the spec's local test stubs, so 3 pm spec examples cannot pass. The TERM
   lane's `tty_service.spl` fix (delete the local extern declaration) is the
   precedent; needs a decision on whether pm unit tests should reach the real
   kernel loader.
7. **Open, handed on:** the two `wm_service_*` specs are red at HEAD with
   `semantic: undefined field 'value': cannot access field on value of type
   'i64'` in the raw-IPC-payload path. Unrelated to this bug, unchanged by this
   lane, and it blocks service-level wm cover (hence the new WmWorld spec).
