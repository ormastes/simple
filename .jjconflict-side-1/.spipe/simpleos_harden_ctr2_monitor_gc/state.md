# Lane CTR2 — container manager increment 2: sys_monitor + sys_gc + §6.4 storage

**Status:** COMPLETE (pure model, no live workload, no QEMU). New spec 13/13 green.
**Date:** 2026-07-27
**Design:** doc/04_architecture/os/container/podman_mdsoc_container_arch.md
           (sys_monitor / sys_gc) + master plan §6.4 (storage)
**Predecessor:** `.spipe/simpleos_harden_t3ctr_manager/state.md` (lane T3-CTR)

## Files

| File | Change |
|---|---|
| `src/os/services/container/container_manager.spl` | extended — sys_monitor, restart policy + sys_restart, sys_gc, store surface |
| `src/os/services/container/container_storage.spl` | NEW — §6.4 image/volume storage model + ref-tracked GC |
| `test/01_unit/os/services/container/container_monitor_gc_spec.spl` | NEW — 13 examples, absolute oracles |

`oci_import.spl`, `container_namespace.spl`, `cspace_spawn.spl` and all kernel
files were NOT touched (import/read only), as scoped.

## What sys_monitor now does

Podman's per-container **conmon** split, modelled exactly: the MONITOR observes,
the MANAGER records.

- New component `MonitorReport(pending, state, exit_code)` — one per Container
  entity; it is the model of the monitor capsule's event port. The monitor
  capsule posts what it saw via `post_monitor_report(idx, state, code)` (states:
  `running` | `exited` | `crashed`).
- `me sys_monitor() -> i64` is a true ECS system: it sweeps the whole world and
  consumes every pending observation, returning how many containers it reaped.
  - `exited` / `crashed` → `Lifecycle = exited(code)` with the **exact** code
    the monitor reported, then **reap**: `MonitorHandle.handle = 0`,
    `last_state = "reaped"`.
  - `running` → only `MonitorHandle.last_state` moves; the lifecycle is untouched.
- **§21 rule applied to containers** (same rule already proven for services):
  the exit tears the authority down in place — kernel view collapsed to
  `container_view_rootless()` (resolves NOTHING), ResourceDomain zeroed,
  `granted_caps` emptied. A crashed container therefore becomes eligible for its
  restart policy while holding **no stale grant at all**.

### Restart without inheritance
- New component `RestartPolicy(policy, max_retries, retries)` — `no` |
  `on-failure` | `always`; `set_restart_policy(idx, policy, max)`.
- `restart_eligible(idx)` = state is `exited` AND retries < max AND
  (policy `always`, or policy `on-failure` with a non-zero code).
- `me sys_restart(idx, reacquired, root, pids, cpu, mem, io, pid_quota)` —
  every grant is supplied AFRESH by the caller: the view is rebuilt from
  `container_view_create(root, pids)`, the resource domain is re-minted, and the
  pouch is the caller's `reacquired` set. Nothing is inherited from the dead
  instance (there is nothing left to inherit — sys_monitor emptied it).
  sys_start's body is INLINED rather than called, to avoid routing a mutation
  through an extra method hop.

## Storage / GC model (`container_storage.spl`, §6.4)

Pure model — no IO, no VFS, no layer unpack. Bookkeeping only; the blocks live
behind the image-store port.

- `ImageLayer(digest, parent, size, ro)` — immutable content-addressed RO layer;
  `parent` is the digest below it in the chain (`""` for a base). `ro` always true.
- `CowSnapshot(layer_id, parent_digest, owner, quota, used, live)` — the
  container's COW writable layer over an RO base, with the **per-container
  quota**. `snapshot_write` refuses (and writes nothing) past quota.
- `Volume(name, dest, persistent, owner, live)` — **explicit** volumes; the
  `persistent` flag is what makes one survive container removal.
- `LayerStore` class holds the three tables directly + a `reclaimed` audit trail.

**Ref-counted GC.** `layer_refcount(store, digest)` counts
1. every **live** `CowSnapshot` whose parent chain passes through the digest
   (chain walk bounded at 64 hops so a cyclic chain cannot wedge the GC), plus
2. every other layer naming it as `parent`.

Released snapshots and already-reclaimed layers contribute nothing.
`gc_collect(store) -> GcOutcome(store, reclaimed)` reclaims **only** layers with
refcount 0, iterating to a fixpoint so a freed leaf cascades to its parent. A
layer a live container uses — directly or deeper in its chain — is never touched.

**Atomic rollback.** `snapshot_rollback(store, container) -> RollbackOutcome`
validates first (live snapshot exists, has a base, base layer present in store);
if any check fails the store is **unchanged** and `ok == false` / `base_digest ==
""`. On success the writable layer is discarded and re-branched (`used = 0`,
`layer_id + ":rb"`) over the SAME base, and the exact base digest is returned.

## What sys_gc now does

`me sys_gc() -> [text]` on `ContainerWorld`:
1. for every container in `exited` or `stopped`: `release_snapshot(owner)` (drops
   the reference its COW snapshot held on the RO base chain) and
   `drop_container_volumes(owner)`, which drops **only non-persistent** volumes —
   explicit persistent volumes survive container removal (Podman/§6.4 rule);
   the `ImageSnapshot` component loses its `cow_layer` but KEEPS `base_digest` so
   the container can be recreated from the same content-addressed base;
2. then `gc_run(false)` — the ref-counted layer collection above.
Returns the reclaimed digests. The store is reached with extract-mutate-writeback
(`var st = self.store; st.…; self.store = st`).

## Spec verdict

`test/01_unit/os/services/container/container_monitor_gc_spec.spl`
via `timeout 300 /tmp/ctr2/bin/ctr2job run <spec>`:

**13 examples, 0 failures** (2 + 3 + 2 + 1 + 3 + 2 across six describes).

Absolute oracles proven:
- exit code recorded **by value**: `lifecycle_exit == 42`; crash `== 137`;
  monitor `"reaped"`; a `running` report never moves the lifecycle.
- crash → `restart_eligible == true` while `granted_of().len() == 0`,
  `allows_path("/c1/app") == false`, `allows_pid(100) == false`,
  `path_decision == "deny"`; after `sys_restart` the pouch is exactly the
  re-acquired `["cap.fs_read"]`, budget `2048`, retries `1`; a clean exit under
  `on-failure` is NOT eligible.
- GC: `refcount("sha256:base") == 1`, `refcount("sha256:orphan") == 0`;
  `sys_gc()` returns exactly `["sha256:orphan"]`; `sha256:base` **survives by
  value** (`store_has_layer == true`, `store_layer_count == 1`). Deeper chain:
  `refcount("sha256:b0") == 2`, `refcount("sha256:b1") == 1`, 0 reclaimed.
- volumes: after `sys_stop` + `sys_gc`, `snapshot_live_of == false`,
  reclaimed `== ["sha256:v"]`, but `volume_live("data") == true` (persistent) and
  `volume_live("scratch") == false`, `live_volume_count == 1`.
- rollback: returns exactly `"sha256:base"`, `used == 0`, layer id
  `"sha256:base:cow:rb"`; with a missing base returns `""` and NOTHING changed
  (`used == 10`, layer id unchanged); quota write refused with `used` unmoved.

**Fail-once proof DONE:** flipping both `gc_run(false)` call sites to
`gc_run(true)` (GC ignores refcounts) turned the ref-tracked GC describe RED —
`2 examples, 2 failures`, the live container's base layer got reclaimed — while
the monitor/rollback describes stayed green. Restored to `false`; re-verified
13/13 green afterwards (`rm -rf .simple/native_cache` between flips).

## Pre-existing specs — do-no-harm (before / after)

Both re-run with the same harness after the changes:

| Spec | Before (lane record) | After (this lane) |
|---|---|---|
| `container_manager_spec.spl` | 7 examples, 0 failures | **7 examples, 0 failures** (4+1+1+1) |
| `oci_import_spec.spl` | 10 examples, 0 failures | **10 examples, 0 failures** (2+6+1+1) |

No regressions. `container_manager.spl` gained fields/systems only; existing
`sys_create` / `sys_pod_wire` / `sys_start` / `sys_stop` signatures are unchanged,
so both pre-existing specs compile and pass untouched.

## Landmines re-confirmed / new

- The cosmetic **"self is implicit"** INFO hint fires on almost every line of the
  new module. It is WRONG here — per lane T3-CTR, removing `self.` in a `me`
  method silently returns a stale read. Kept everywhere; ignore the hint.
- `bin/simple lint` is BROKEN on these class-based modules: it reports
  `error: semantic: method 'get' not found on type 'str' (receiver value:
  LayerStore)` / `(receiver value: ContainerWorld)` — the receiver is a class but
  the linter typed it `str`. **Pre-existing**: the same failure reproduces on the
  untouched `container_manager.spl` shape and `oci_import.spl` also fails lint.
  Not caused by this lane; the runtime spec is the verdict.
- `gc_collect` calls `s.gc_run(false)` DIRECTLY, not via the `gc()` convenience
  wrapper, so the mutation is never routed through an extra method hop.
- `sys_restart` inlines `sys_start`'s body for the same reason.

## Blockers

- **NO live workload evidence.** `sys_monitor` consumes a posted `MonitorReport`;
  there is no real monitor capsule, no `waitpid`-equivalent, no spawn broker.
  The monitor capsule spawn is still gated on the `AT_SIMPLE_CSPACE` injection
  ABI (P2/P3, boot-toolchain-blocked) per `cspace_spawn.spl`.
- **NO QEMU / board evidence** — pure model, no boot, no disk. The storage model
  does zero IO: no real layer blocks, no VFS, no power-fail/atomicity evidence on
  a real filesystem. Per §6.4 the custom overlay stays OUT of the security
  boundary until power-fail recovery + namespace-escape tests pass; this lane
  does not move that bar.
- No signed metadata (§6.4 mentions it) — digest verification/signing is not
  modelled here; it belongs with the image-import path.

## Next increment

1. Wire `sys_monitor` to a real per-container monitor capsule (event port +
   exit notification) once the spawn broker lands; keep `post_monitor_report`
   as the test seam.
2. Back `LayerStore` with the real image-store VFS port: content-addressed layer
   files, real COW block accounting, signed layer metadata / digest verification.
3. Power-fail atomicity evidence for `snapshot_rollback` on a real filesystem —
   the §6.4 gate for letting the overlay near the security boundary.
4. QEMU boot evidence for a full container create → start → crash → restart →
   stop → gc cycle, then the board-runnable path (`.claude/rules/board-runnable.md`).
