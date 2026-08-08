# Lane T3-CTR — Podman-design container manager (MDSOC+ userland capsule)

**Status:** first increment COMPLETE (pure model, no QEMU). Spec 7/7 green.
**Date:** 2026-07-27
**Design:** doc/04_architecture/os/container/podman_mdsoc_container_arch.md

## What was built

### Capsule + ECS World
`src/os/services/container/container_manager.spl` — the container-manager MDSOC+
capsule. MDSOC outer boundary is documented in the module header (ports:
control/image-store/kernel-spawn/event; caps: image-store VFS + spawn broker +
resource-domain mint, NO host root / NO ambient net). Inner business layer is an
ECS `ContainerWorld` (plain component structs + parallel component arrays keyed
by entity index; one Container entity == one array index). Chose plain-array ECS
(not std.ecs ComponentStore) for seed-run robustness and to sidestep the
two-struct-field-hop mutation defect.

**Components (data-only structs):** ContainerId(id,name),
PodMembership(pod_id,shared_ns_mask), NamespaceView(view:kernel
ContainerNamespaceView + net_handle/ipc_handle), ResourceDomain(cpu,mem,io,pids),
ImageSnapshot(base_digest,cow_layer,quota), Lifecycle(state,exit_code),
MonitorHandle(handle,last_state). Side table: Pod(id,net_handle,ipc_handle).
Model of the kernel SpawnSpec: ContainerSpec + SpawnRequest + caps_is_subset().

### Systems (all IMPLEMENTED, none stubbed for this increment)
- `sys_create` — begins from `container_view_rootless()` (deny-everything), then
  adds ONLY the declared root+pids via `container_view_create`. COW snapshot +
  ResourceDomain + Lifecycle="created". No start. (Has a `seed_global_root`
  defect-injection param, default false, used only for the fail-once proof.)
- `sys_pod_wire` — shares the pod's net/ipc endpoint handles per shared_ns_mask
  bits; the kernel view (mount/pid) is passed through UNCHANGED — never widened.
- `sys_start` — builds ContainerSpec from view+domain, maps to SpawnRequest whose
  caps == granted (a subset, never amplified); Lifecycle="running" + MonitorHandle
  attached. Does NOT call the live spawn syscall (model only).
- `sys_stop` — ordered revocation mirroring driver §7.3: stop scheduling → revoke
  net/ipc endpoints → (device grants/volumes folded into) collapse kernel view to
  rootless → collect exit → free resource domain → drop granted pouch. §21
  invariant enforced: the view resolves NOTHING afterward.

Stubbed / deferred (next increment): sys_oci_import, sys_monitor (poll loop),
sys_gc (layer ref-count reclaim).

## How kernel enforcement is consumed
The manager imports and DELEGATES to the T2-A kernel primitive
(`src/os/kernel/loader/container_namespace.spl`) — it never re-implements
namespace lookup. `ContainerWorld.allows_path/allows_pid/path_decision/
pid_decision` call `container_view_allows_path` / `container_view_allows_pid` /
`container_view_path_decision` / `container_view_pid_decision` on the stored
kernel `ContainerNamespaceView`. The kernel view IS the spec oracle; the manager
only constructs the handles the kernel enforces. container_namespace.spl was NOT
modified (import-only, as scoped).

## Spec verdict
`test/01_unit/os/services/container/container_manager_spec.spl`
**7 examples, 0 failures** via `/tmp/t3ctr/bin/t3job run <spec>`.
Proves: rootless-by-construction (allow /c1/app; deny /c2/x, escape /c1/../c2/x,
pid 999); pod net/ipc shared but mount private (A cannot resolve B's /cb path);
daemonless subset (caps_is_subset(req.caps, granted)==true; amplified set
rejected); stop-revocation (post-stop denies every previously-allowed path/pid,
domain freed, monitor reaped, pouch dropped).

**Fail-once proof done:** forcing sys_create to seed a global "/" root flipped the
whole suite to 4+3 failures (deny oracles broke); restored to green.

## Landmines recorded
- In `me` methods, the final return expression MUST keep `self.` (e.g.
  `self.ids.len() - 1`, `self.lifecycles[idx]`). The compiler emits an INFO
  "self is implicit" hint, but REMOVING `self.` silently changes semantics — a
  bare implicit-self read of a just-written field returned stale/empty and turned
  the suite fully red. The info hint is cosmetic; do not act on it here.
- Harness native-cache can serve a stale compile across an edit; `rm -rf
  .simple/native_cache` + touch when a restore appears not to take.

## Blockers
- NO live spawn evidence: sys_start produces a SpawnRequest model, not a real
  kernel SpawnSpec submission; the spawn broker / AT_SIMPLE_CSPACE injection ABI
  is P2/P3 and boot-toolchain-blocked (per cspace_spawn.spl header). This is the
  LOGIC/model tier only.
- NO QEMU / board evidence — pure model, no boot. Board-runnable path is a future
  increment once sys_start wires to the real broker.

## Next increment
1. `sys_oci_import` — OCI bundle → ContainerSpec edge adapter with fail-closed
   path/symlink/device checks.
2. Wire `sys_start` to the real spawn broker: map ContainerSpec caps → kernel
   `CapGrant`/`SpawnSpec` (os.kernel.ipc.cspace_spawn) and mint an attenuated
   child C-Space; attach a real Monitor capsule.
3. `sys_monitor` + `sys_gc`; then QEMU boot evidence for a container start/stop.
