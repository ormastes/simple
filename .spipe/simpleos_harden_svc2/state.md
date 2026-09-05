# SimpleOS Harden — SVC2b: real services declare service_v1 manifests

## Status: DONE (uncommitted) — 2026-07-27

Closes the `service_manifest:` ledger gap "real services declaring manifests
pending" in `doc/08_tracking/os/production_status.sdn`.

## Phases
- [x] research — read `src/os/services/service_manifest.spl` (typed service_v1
      lifecycle/health/watchdog/restart-limit + §21 restart-drops-stale-grants)
- [x] implement — two REAL services now declare and use a manifest
- [x] verify — new integration spec green + all related specs re-run green
- [x] ship — ledger note updated; NOT committed (lane instruction)

## Blocker found and repaired (outside the original lane scope)

`src/os/services/container/container_manager.spl` imports
`ContainerNamespaceView` / `container_view_rootless` / `container_view_create` /
`container_view_allows_path` / `container_view_allows_pid` /
`container_view_path_decision` / `container_view_pid_decision` from
`os.kernel.loader.container_namespace`. **Those symbols existed nowhere in the
repo.** The file at that path holds an unrelated same-named module (the
desktop-e2e wine-container contract), so at HEAD:

    container_manager_spec       5 blocks, 8/8 FAILING
    container_monitor_gc_spec    RED (same import)
    oci_import_spec              RED (same import)

all with `semantic: function 'container_view_rootless' not found`. The lane
brief assumed these were green at HEAD; they were not.

Repair: the kernel primitives were **appended** (never replacing an existing
symbol) to `src/os/kernel/loader/container_namespace.spl`, with semantics taken
verbatim from the absolute oracles in `container_manager_spec.spl`:
rootless denies all paths and pids; a view rooted at R allows exactly R and
paths at/below `R/`; any path containing `..` is REFUSED without normalization;
a view sees only its declared pids. If lane T2-A lands the real module, this
block is the one to reconcile against.

## What was implemented

### 1. container-manager (`src/os/services/container/container_manager.spl`)
- `fn container_manager_manifest() -> ServiceManifest` — declares
  name `container-manager`, version `service_v1`,
  required_capabilities `[cap.spawn, cap.fs_mount, cap.resource_domain]`,
  readiness_deps `[vfs, pm]`, health `heartbeat`, policy `on_failure`,
  max_restarts `3`, watchdog `5000ms`.
- `ContainerWorld.manifest: ServiceManifest` — held DIRECTLY (single field hop).
- Lifecycle hooks mapped onto the EXISTING machinery (no second mechanism):
  `svc_start(ready_set)` (refuses until vfs+pm are up), `svc_acquire_grant`,
  `svc_ready`, `svc_heartbeat`, `svc_watchdog`, `svc_health_check`,
  `svc_restart_allowed`, `svc_restart`, `svc_stop`, plus read-only accessors.
- Health comes from the manager's OWN world invariants (`svc_world_invariant`):
  the service is healthy exactly while every stopped/exited container holds an
  empty capability pouch AND resolves nothing (view collapsed to rootless).
- **§21 on the restart path** (`svc_restart`): `on_restart()` clears the
  manifest's `granted_handles`, AND the authority the manager had brokered out
  is torn down — every container's `granted_caps` emptied and every kernel view
  collapsed to `container_view_rootless()`. Refuses (no state change) once
  `max_restarts` is spent.

### 2. tty service (`src/os/services/tty_service.spl`)
- `fn tty_service_manifest() -> ServiceManifest` — name `tty`, version
  `service_v1`, required_capabilities `[dev.console, dev.serial]`,
  readiness_deps `[ds]`, health `heartbeat`, policy `always`,
  max_restarts `5`, watchdog `2000ms`.
- `TtyService.manifest: ServiceManifest` + the same hook set.
- **§21 restart hook**: `on_restart()` drops the device grants, and EVERY TTY's
  `pending_signal` / `pending_signal_pgrp` is cleared. A pending SIGINT is
  authority aimed at a pgrp resolved by the PRE-restart instance; surviving a
  restart it would fire at whatever process group now owns that number.
  `session_id` / `foreground_pgrp` are deliberately PRESERVED — that is the
  controlling-terminal binding, not pending authority.

Every manifest mutation uses extract-mutate-writeback
(`var m = self.manifest; m = f(m); self.manifest = m`) and the per-TTY clear
goes through `var ctl_store = self.world.term_ctls; var d = ctl_store.dense;
...; ctl_store.dense = d; self.world.term_ctls = ctl_store` — bug
`selfhost_two_hop_field_method_mutation_lost_2026-07-27` silently discards a
`self.<a>.<b>.mutate()` chain crossing an imported struct.

## Verification (`build/native_probe/simple run <spec>`)

New — `test/01_unit/os/services/service_manifest_integration_spec.spl`:
**9 describe blocks, 16 examples, 0 failures.**

Regression (all re-run after the change):

| spec | blocks | examples | failures |
|---|---|---|---|
| container/container_manager_spec.spl | 5 | 8 | 0 |
| container/container_monitor_gc_spec.spl | 6 | 13 | 0 |
| container/oci_import_spec.spl | 4 | 10 | 0 |
| tty_service_spec.spl | 8 | 18 | 0 |
| tty_termios_ld_spec.spl | 5 | 16 | 0 |
| service_manifest_spec.spl | 5 | 11 | 0 |

The three container specs were RED before the kernel-primitive repair.

## Files touched
- `src/os/kernel/loader/container_namespace.spl` (append-only repair)
- `src/os/services/container/container_manager.spl`
- `src/os/services/tty_service.spl`
- `test/01_unit/os/services/service_manifest_integration_spec.spl` (new)
- `doc/08_tracking/os/production_status.sdn` (`service_manifest:` note only)

## Follow-ups
- Reconcile the appended `ContainerNamespaceView` primitives with lane T2-A's
  real kernel module if/when it lands.
- Wire the two manifests into `src/os/kernel/boot/init_services.spl` so the
  boot supervisor evaluates them instead of the ad-hoc per-service `ready()`
  bools (the stated purpose of the service_v1 model).
