# Bug: mutating method call two struct-field hops from `self` silently loses the write (self-hosted binary)

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent state loss; systemic for ECS-style services)
- **Found by:** SimpleOS harden lane P4 (TTY), reproduced in isolation

## Symptom
`self.world.output_bufs.insert(...)` — a mutating method invoked on a value
reached through TWO field hops from `self` — executes without error but the
mutation does not persist in `self.world.output_bufs`. One-hop mutations
persist. Reproduced with a minimal standalone repro by the lane (see
`.spipe/simpleos_harden_p4_tty/state.md`).

## Scope
- Observed on the self-hosted binary lane (`build/native_probe/simple`).
- Pre-existing: already silently affecting `tty_create`'s component stores and
  the pre-existing `tty_service_spec.spl` before this session's edits.
- Likely affects every ECS/ComponentStore-style SimpleOS service that mutates
  `self.<world>.<store>` chains — same value-copy semantics class as
  "arrays are value types" but here the intermediate struct copy is silent.

## Workaround (used in `src/os/services/tty_service.spl`)
Extract-mutate-writeback:
```
var s = self.world.output_bufs
s.insert(...)
self.world.output_bufs = s
```

## Second confirmed instance (2026-07-27, lane PTY2) — entity allocator
`TtyService.tty_create` called `self.world.base.spawn()`, which mutates
`WorldBase.alloc: EntityAllocator` internally. Because that is also a two-hop
chained mutating call, **every spawned entity came back as the SAME
`Entity(id:0, generation:1)`** as soon as one world created more than one TTY.
Single-TTY specs never noticed; a cross-talk test with 2 PTY pairs (4 entities)
exposed it. Same workaround applied (`var base = self.world.base; val e =
base.spawn(); self.world.base = base`).

This makes the defect **systemically dangerous for every ECS service**: it
silently collapses entity identity rather than merely dropping a write. The root
fix belongs in the ECS world owner (`src/lib/*/ecs/world.spl`) plus the compiler
lowering below.

## Next step
Root-cause in the self-hosted compiler's place/lvalue lowering for chained
field receivers of mutating methods; add a regression spec with the minimal
two-hop repro. Related class: value-type copy on method receiver chains.

## Swept 2026-07-27 (lane ECS2 — container/manifest/llm/vfs/llm_profiles)

Sweep of `src/os/services/container/**`, `src/os/services/service_manifest.spl`,
`src/os/services/llm/**`, `src/os/services/vfs/**`,
`src/os/security/llm_profiles/**` for `self.<f>.<f>.<mutating>()` and
`<var>.<f>.<f>.<mutating>()` chains. (`tty_service.spl` excluded — owned by
lane P4/PTY2, already fixed.)

### Trigger boundary narrowed (probes, both `build/ecs2_job` = release
self-hosted and `build/native_probe/simple`):
- Single-file struct OR class two-hop chains (var-rooted and self-rooted):
  writes PERSIST. Probes: `build/ecs2_twohop_probe.spl`, `_probe2.spl`.
- **Cross-module** imported ECS types (`use nogc_sync_mut.ecs.*`), self-rooted
  `self.world.base.spawn()` / `self.world.foos.insert(...)`: REPRODUCED —
  every spawn returns Entity(id:0, gen:1), inserts lost (get_slot = -1).
  Probe: `build/ecs2_twohop_probe3.spl`. (Probe also shows `main()` executes
  twice under `run` — separate oddity, not investigated.)
- Cross-module CLASS→CLASS two-hop (`self.bridge.session.<mutating>()` shape):
  writes PERSIST on both binaries. Probe: `build/ecs2_twohop_probe4.spl` +
  `build/ecs2_mod_inner.spl`. So class-reference chains are safe; the hazard
  is struct-valued intermediates with cross-module-imported types.

### Sites fixed
None — zero live hazard instances found in the swept trees.

### Sites audited clean
- `src/os/services/container/container_manager.spl` — designed around the bug
  (header lines 12-20: world holds component arrays DIRECTLY, single hop +
  extract-mutate-writeback). No two-hop chains present.
- `src/os/services/container/container_storage.spl`, `oci_import.spl` — no
  `self.<f>.<f>.` chains at all.
- `src/os/services/service_manifest.spl` — functional style (`_clone`/`mark_*`
  return new manifests); structurally immune, no chains.
- `src/os/security/llm_profiles/{profile_registry,profile_spawn_adapter}.spl`
  — no `self.<f>.<f>.` chains.
- `src/os/services/vfs/**` — only two-hop READ (`vfs_service.spl:401`
  `self.vfs.mounts.len()`) and one-hop trait-object calls
  (`mount.fs.write/read/close` — `fs: Filesystem` is a trait object). Clean.
- `src/os/services/llm/_McpOsServer/ui_access_tools.spl` (85, 177, 229, 292,
  295) and `dispatch_and_io_tools.spl` (330, 355, 356, 371, 373, 375, 417,
  447, 448, 476, 477) — `self.bridge.session.<mutating>()`; both `CliGuiBridge`
  and `UISession` are `class` (reference), proven safe by probe4 above.

### Regression spec added
`test/01_unit/os/services/container/container_manager_spec.spl` — new
"cross-entity identity (two-hop mutation-loss regression)" block: 3 containers
in one world, asserts distinct indices 0/1/2, per-entity path/pid/caps
isolation, and start/stop of one sibling not leaking. 8 examples, 0 failures
on `build/ecs2_job`.

### Out-of-scope observation (for other lanes / coordinator)
These files import `WorldBase`/`ComponentStore` and are in the reproduced
hazard class but were NOT in lane ECS2's assigned trees — they still need
their own sweep: `src/os/services/{ds,devfs,pipefs,clock,procfs,sched,rs,pm}_service.spl`,
`devfs_filesystem.spl`, `procfs_filesystem.spl`, `wm/wm_world.spl`,
`wm/wm_service.spl`, `fs_apps/app_loader_world.spl`, and
`src/os/apps/{calculator,clock,hello_world}/**`.
