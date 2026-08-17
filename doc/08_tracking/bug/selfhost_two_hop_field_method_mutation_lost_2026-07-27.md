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
> **CORRECTED 2026-07-27** — the "cross-module / imported-struct" framing in this
> section and in the ECS2 sweep below is an ARTIFACT. The defect is in the
> INTERPRETER's place model and applies to ANY chain of depth >= 2, struct or
> class, same-file or cross-module. See "ROOT CAUSE (lane THFIX2)" below and
> "ECS2 re-verification" for the probe matrix. Do not cite the module-boundary
> theory.

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

### ~~Trigger boundary narrowed~~ — RETRACTED 2026-07-27, was an artifact
The original ECS2 probes were all run through `main()`, which the default engine
JIT-compiles — and **JIT is correct at every depth**. So every "writes PERSIST"
result below was measuring the healthy engine, not the defective one. Retracted
claims:
- ~~"Single-file struct OR class two-hop chains: writes PERSIST"~~ — FALSE.
- ~~"class-reference chains are safe"~~ — FALSE. Classes are equally affected.
- ~~"the hazard is struct-valued intermediates with cross-module-imported
  types"~~ — FALSE. Neither the module boundary nor struct-vs-class matters.

### ECS2 re-verification (2026-07-27, corrected premise)
Same probes re-run with `SIMPLE_EXECUTION_MODE=interpreter` to reach the
defective engine. `INTERP` / `JIT` = value observed after 2 mutations (want 2):

| shape | probe | JIT | INTERP |
|---|---|---|---|
| zero/one-hop, struct or class, any root | `ecs2_classdepth.spl` A,B | 2 | **2 (safe)** |
| single-file struct two-hop | `ecs2_twohop_probe.spl` | 2 | **0 (LOST)** |
| single-file class two-hop | `ecs2_twohop_probe.spl` | 2 | **0 (LOST)** |
| self-rooted struct/class two-hop | `ecs2_twohop_probe2.spl` | 2 | **0 (LOST)** |
| cross-module class→class two-hop | `ecs2_twohop_probe4.spl` | 2 | **0 (LOST)** |
| three-hop | `ecs2_fixcheck.spl` | 2 | **0 (LOST)** |

Conclusions (all probe-proven, consistent with lane THFIX2's root cause):
1. **Depth is the only axis that matters.** Depth 0-1 safe; depth >= 2 loses the
   write. Struct vs class, same-file vs cross-module, var- vs self-rooted are
   all irrelevant.
2. **Extract-mutate-write-back is a VALID fix on the defective engine** —
   verified at both two and three hops (`ecs2_fixcheck.spl`: FIXED two-hop = 2,
   FIXED three-hop = 2 under INTERP).
3. **Extraction ALONE is not enough.** `val s = self.bridge.session; s.bump()`
   still loses the write (`ecs2_classdepth.spl` case D = 0), because the
   extraction is itself a depth-2 read yielding a copy. The write-back is the
   load-bearing half — each hop must be stepped one level at a time.
4. **Delegation is an equally valid fix** — moving the mutation into a method on
   the intermediate so each call site is one hop (`ecs2_classdepth.spl` case
   F = 2 under INTERP).
5. **Spec `it` blocks always evaluate on the interpreter**, regardless of
   `SIMPLE_EXECUTION_MODE`. So a spec asserting a raw depth>=2 mutation fails
   even when the same code works from `main()`. This is the mechanism behind the
   known "passes in main, fails under `it`" landmine, and it means the whole
   suite runs on the defective engine.

### Sites fixed
None — zero live hazard instances found in the swept trees.

### Sites audited clean (re-audited 2026-07-27 under the corrected premise)
Re-audit rule applied: count FIELD hops before the method call. `x.m()` and
`x.f.m()` are safe; `x.f.g.m()` and deeper lose the write. Reads at any depth
are safe. All entries below were re-checked against that rule and still hold,
EXCEPT the llm `_McpOsServer` entry, which moved out of this list (above).
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
  `self.vfs.mounts.len()`), which is safe. Mutating calls are all one field hop:
  `self.vfs.resolve_mount(...)` (`self`→`vfs`, then method) and
  `mount.fs.write/read/close` where `mount` is a LOCAL bound at :314/:329/:347/
  :367/:385 (`mount`→`fs`, then method). Clean — re-confirmed, not resting on
  the retracted trait-object/class argument but on hop depth.
### Verdict CHANGED by the corrected premise — llm `_McpOsServer`
- `src/os/services/llm/_McpOsServer/ui_access_tools.spl` (85, 177, 229, 292,
  295) and `dispatch_and_io_tools.spl` (330, 355, 356, 371, 373, 375, 417,
  447, 448, 476, 477) — `self.bridge.session.<mutating>()`.
  **Previously marked "audited clean" solely because probe4 said class chains
  were safe. That basis is now retracted, so these are RECLASSIFIED to
  HAZARD-SUSPECT (depth-2 mutating chains: `set_active_surface`, `dispatch`,
  `open_surface`, `bind_window_surface`, `close_surface`,
  `clear_window_surface_binding`, `clear_window_binding`, `update_surface_tree`,
  `set_surface_widget_value`).** The two-hop *reads* on these same lines
  (`access_snapshot`, `has_surface`, `surface_handle`, `get_surface`, …) are
  fine — a copied receiver still reads correctly; only writes are lost.
  **NOT FIXED — verification is blocked** by a pre-existing, unrelated red in
  the only covering spec, `test/01_unit/os/services/llm/ui_access_dispatch_spec.spl`:
  13 examples / 13 failures, all `semantic: function expects argument for
  parameter 'children'` (API drift against `src/lib/common/ui/builder.spl`,
  outside lane ECS2's trees). Edits were deliberately NOT made blind against a
  spec that cannot green. Recommended fix once unblocked: delegation (add
  mutating wrappers to `CliGuiBridge` so each call site is one hop), which is
  ~9 methods versus ~15 write-back call-site rewrites.

### Spec verification (2026-07-27, corrected premise)
All re-run on `build/native_probe/simple run`. Because spec `it` bodies always
evaluate on the interpreter, these results are against the DEFECTIVE engine —
i.e. the extract-mutate-write-back fixes are proven where it counts:

| spec | result |
|---|---|
| `os/services/clock_service_spec.spl` | 3 examples, 0 failures |
| `os/services/devfs_service_spec.spl` | 3 examples, 0 failures |
| `os/services/ds_service_spec.spl` | 4 examples, 0 failures |
| `os/services/pipefs_service_spec.spl` | 3 examples, 0 failures |
| `os/services/procfs_service_spec.spl` | 2 examples, 0 failures |
| `os/services/rs_service_spec.spl` | 3 examples, 0 failures |
| `os/services/service_manifest_integration_spec.spl` | 1 example, 0 failures |
| `os/services/container/container_manager_spec.spl` | 1 example, 0 failures |

Pre-existing reds observed, NOT caused by this sweep and NOT fixed:
- `test/01_unit/os/services/llm/ui_access_dispatch_spec.spl` — 13/13 failing on
  `parameter 'children'` API drift (`src/lib/common/ui/builder.spl`); blocks
  verification of the llm reclassification above.
- `test/01_unit/compiler/two_hop_field_method_mutation_spec.spl` (lane THFIX) —
  5 examples / 4 failures in BOTH engine modes. Expected: it is the regression
  spec for this still-open bug, and its `it` bodies run on the interpreter. It
  should go green when the place-model fix lands, and is the natural gate for it.

### Regression spec added
`test/01_unit/os/services/container/container_manager_spec.spl` — new
"cross-entity identity (two-hop mutation-loss regression)" block: 3 containers
in one world, asserts distinct indices 0/1/2, per-entity path/pid/caps
isolation, and start/stop of one sibling not leaking. 8 examples, 0 failures
on `build/ecs2_job`.

### Out-of-scope observation (for other lanes / coordinator) — UPDATED 2026-07-27
The original triage criterion here ("imports `WorldBase`/`ComponentStore`") is
superseded. **The correct criterion is purely structural: any mutating call
reached through >= 2 field hops, in any file, regardless of imports, and
regardless of struct vs class.** An ECS import is neither necessary nor
sufficient — it merely made the fallback to the interpreter more likely by
bailing JIT lowering.

Since swept and fixed (specs green, table above):
`src/os/services/{ds,devfs,pipefs,clock,procfs,sched,rs}_service.spl`.

Still unswept under the widened criterion, for other lanes:
`pm_service.spl`, `devfs_filesystem.spl`, `procfs_filesystem.spl`,
`wm/wm_world.spl`, `wm/wm_service.spl`, `fs_apps/app_loader_world.spl`,
`src/os/apps/{calculator,clock,hello_world}/**`, plus the llm `_McpOsServer`
files reclassified above. Because the criterion is now structural rather than
import-based, a repo-wide grep for `\.\w+\.\w+\.\w+(` (mutating tail) is the
right net, not a search for ECS importers.

## ROOT CAUSE (lane THFIX2, 2026-07-27) — it is the INTERPRETER, not hop count or module boundary

The "cross-module two-hop" boundary reported above is an artifact. The real
rule, proven by a construction/depth/engine matrix (`build/thfix_probe_*.spl`):

| case | JIT (default `run`) | interpreter |
|---|---|---|
| zero-hop `v.bump()` | persists | persists |
| one-hop `v.f.bump()` | persists | persists |
| **two-hop `v.f.g.bump()`** | **persists** | **LOST (0)** |
| **three-hop** | **persists** | **LOST (0)** |
| extract-mutate-write-back | persists | persists |
| two-hop direct assign `v.f.g.n = 5` | works | **hard error** |

Module boundary, struct vs class, `me` vs `fn(self)` on the *called* method,
field/struct/method names, and constructor form are all irrelevant — a
single-file probe under `SIMPLE_EXECUTION_MODE=interpreter` loses the write
(`build/thfix_probe_depth_clean.spl`).

### Decision point
The interpreter's place model is hand-written for at most **2 levels** of field
place, rooted at a plain variable name. `src/compiler_rust/compiler/src/interpreter/node_exec.rs:944-947`
rejects a deeper *assignment* loudly:

> `invalid assignment: deeply nested field access requires intermediate variables`
> help: `deeply nested field assignment (more than 2 levels) is not supported; use intermediate variables`

The **method-call receiver path has no equivalent guard**. The same unsupported
place is silently evaluated as a value copy, the method mutates the copy, and
the copy is discarded — no write-back. Loud on assignment, silent on the
method spelling of the identical operation. Pure-Simple counterpart of the
2-level place model: `src/compiler/10.frontend/core/interpreter/eval_access.spl:303-325`
(field-assign) vs `_EvalOps/call_method_eval.spl:569-647` (receiver evaluated
once at :574, never stored back).

### Why it looked cross-module-only
`src/lib/nogc_sync_mut/ecs/**` declares mutating methods with the **explicit-self
form** — `world.spl:29 fn spawn(self)`, `component_store.spl:39 fn insert(self, ...)`,
`change_detection.spl:29 fn push_removed(self, ...)`, `system.spl:18 fn add(self, ...)`.
A mutating `fn X(self)` is a hard HIR error:

> `HIR lowering error: cannot modify self in immutable fn method 'Zmut.poke'. Use ` + "`me`" + ` instead of ` + "`fn`" + ` to allow self mutation`

That error makes **JIT lowering bail for the whole program**, and the driver
falls back to the interpreter with only an `[INFO]` line
(`[INFO] JIT compilation failed, falling back to interpreter`). So *any* program
importing ecs runs interpreted, where two-hop writes are lost. Importing a
one-line module with a mutating `fn X(self)` reproduces the "cross-module" loss
for a purely local, same-file two-hop chain (`build/thfix_p_selfmut.spl`) — that
is the whole mechanism.

### Fix, in priority order
1. **Make the silent case loud.** Apply the `node_exec.rs:944` depth guard to
   method-call receivers too. Cheapest, removes the silent-corruption class.
2. **Give the interpreter a real place model** — evaluate a receiver
   field-chain to (root env slot, field path) and write back after the call at
   any depth, instead of the fixed 2-level special cases.
3. **Stop the fail-soft JIT bail from being silent.** `[INFO] JIT compilation
   failed, falling back to interpreter` should be a warning naming the offending
   declaration; degrading the whole program's semantics deserves more than INFO.
4. **`src/lib/nogc_sync_mut/ecs/**`: change mutating `fn X(self)` to `me X()`.**
   Not this lane's path, but it is the single change that would have prevented
   every reported ECS symptom, and it also unblocks the JIT for every ecs
   consumer. Same sweep applies to any other lib using mutating `fn(self)`.
5. Retain the extract-mutate-write-back workarounds; the spec below asserts they
   stay equivalent to the direct form.

### Regression spec (deliberately RED)
`test/01_unit/compiler/two_hop_field_method_mutation_spec.spl` +
`test/fixtures/two_hop_mutation/inner_types.spl`. Result on
`bin/release/x86_64-unknown-linux-gnu/simple test`: **5 examples, 4 failures** —
one-hop green, all two-hop cases red. Red is correct and expected: `simple test`
runs specs on the interpreter, so the suite as a whole executes on the defective
engine. It goes green when fix 1 or 2 lands.

## Swept 2026-07-27 (lane ECS3 — remaining SimpleOS service worlds)

Executed the ECS2 handoff list: `src/os/services/{ds,devfs,pipefs,clock,procfs,
sched,rs,pm}_service.spl`, `devfs_filesystem.spl`, `procfs_filesystem.spl`,
`wm/wm_world.spl`, `wm/wm_service.spl`, `fs_apps/app_loader_world.spl`, and
`src/os/apps/{calculator,clock,hello_world}/**`. Binary: `build/native_probe/simple`.

### Sites fixed (extract-mutate-writeback)
All are `self.world.<store>.<mutating>()` / `self.world.base.spawn|despawn|advance()`
chains crossing the imported `WorldBase` / `ComponentStore<T>` types.

- `ds_service.spl` — `ds_publish` (spawn + 5 inserts + same-owner endpoint/ttl
  update), `ds_unpublish`/`sys_gc_expired` (factored into new `remove_entry`,
  5 removes + despawn), `ds_subscribe`, `ds_unsubscribe`, `ds_advance`.
- `devfs_service.spl:89,117` — `dev_register` (spawn + 5 inserts),
  `dev_unregister` (5 removes + despawn).
- `pipefs_service.spl:89,109,123,138` — `pipe_create` (spawn + 5 inserts),
  `pipe_write_notify`, `pipe_read_notify`, `pipe_close`.
- `procfs_service.spl:106` — `procfs_node_register` (spawn + 3 inserts).
- `rs_service.spl:105,128,134,162,178` — `rs_register` (spawn + 5 inserts),
  `rs_heartbeat`, `rs_advance`, `sys_check_heartbeats`, `rs_restart`.
- `clock_service.spl:143,154,164,174,187,102,105` — the three `clock_arm_*`
  methods (factored into one `arm_alarm` helper), `clock_cancel`,
  `clock_service_tick`, and both branches of `sys_fire_due_alarms`.
- `sched_service.spl:227,243,260,281,286,139,164,191` — `sched_register_task`,
  `sched_unregister_task`, `sched_record_usage`, `sched_set_nice`, `sched_tick`,
  and both systems.
- `pm_service.spl:250,284,317,330,350` — `pm_fork` (spawn + 8 inserts),
  `pm_exec`, `pm_waitpid`, `pm_exit`, `pm_kill`.
- `wm/wm_service.spl:446,500,517,534` — `parse_resize` geometry write and the
  `parse_minimize`/`parse_maximize`/`parse_restore` state writes.

### Three adjacent defects the fix UNMASKED (all fixed here)
1. **Struct-valued world passed by value into a system function.**
   `sys_fire_due_alarms(world: ClockWorld)`, `sys_demote_runaway_drivers` and
   `sys_age_priorities(world: SchedWorld)` mutated a *copy*; every write was
   discarded at return. Signatures now take `world_in` and `-> ClockWorld` /
   `-> SchedWorld`, and callers write the result back. This is the same
   value-copy class one level up from the two-hop bug and is invisible until
   entity identity works.
2. **`Entity(id: 0)` used as a "not found" sentinel.**
   `sched_service.find_entity_for_task` returned `Entity(id: 0, generation: 0)`
   when no task matched, and four callers tested `if e.id == 0`. Once spawn
   stopped collapsing to id 0, the *first registered task* legitimately owns
   id 0 and became permanently unreachable. Now returns `Entity.null()` and
   callers use `e.is_null()`. **Any other service using an id-0 sentinel has
   the same latent bug.**
3. **Dangling `extern fn` declarations with no implementation anywhere.**
   `clock_notify` (clock_service) and `sched_mechanism_set_priority`
   (sched_service) aborted with `unknown extern function` the moment a real
   alarm fired / a real driver was demoted. Masked because nothing was ever
   armed or registered. Both replaced with the `ds_notify`-style module stub +
   counter + `*_count_value()` accessor. (Same shape the TERM lane applied in
   `tty_service.spl`.)

### Sites audited clean
- `devfs_filesystem.spl`, `procfs_filesystem.spl`, `fs_apps/app_loader_world.spl`
  — no `<a>.<b>.<mutating>()` chains at all.
- `wm/wm_world.spl` — all ECS mutation is one hop from `self` *inside* `WmWorld`
  (`self.base.spawn()`, `self.win_ids.insert(...)`), the proven-safe shape.
- `src/os/apps/{calculator,clock,hello_world}/ecs/world.spl` and their
  top-level `*.spl` — same one-hop-inside-own-world shape; no two-hop chains.
- `pm_service.PmWorld.spawn_process` — one hop from `self` inside `PmWorld`.
- `ds/devfs/pipefs/procfs/rs/clock/sched/pm/wm_service` re-grepped after the
  edits: zero remaining `self.<a>.<b>.<mutating>()` chains.

### Wrong spec expectations corrected
Six specs asserted `expect(e.id).to_be_greater_than(0)` on the FIRST entity of a
fresh world. `EntityAllocator` hands out id **0** first, so this expectation was
always wrong — it only "passed" while two-hop mutation loss made allocator state
unobservable. Replaced with absolute `id == 0`, `generation == 1`,
`is_null() == false` in ds / devfs / pipefs / procfs / clock / sched specs.

### Regression specs added (all `build/native_probe/simple run`, every summary
### line 0 failures)
| Spec | New block | Verdict |
|------|-----------|---------|
| `test/01_unit/os/services/ds_service_spec.spl` | 4 examples: distinct ids 0/1/2, endpoint isolation, unpublish-one, per-entity subscriber lists | 19 examples, 0 failures |
| `.../devfs_service_spec.spl` | 3 examples: ids 0/1/2, per-device endpoint+mode, unregister-middle | 15 examples, 0 failures |
| `.../pipefs_service_spec.spl` | 3 examples: ids 0/1/2, per-pipe buffered bytes, per-pipe close bits | 19 examples, 0 failures |
| `.../procfs_service_spec.spl` | 2 examples: ids 0/1/2, per-node pid isolation | 13 examples, 0 failures |
| `.../rs_service_spec.spl` | 3 examples: ids 0/1/2, per-capsule restart budget, per-capsule liveness+crash reason | 21 examples, 0 failures |
| `.../clock_service_spec.spl` | 3 examples: ids 0/1/2, cancel-one, three alarms firing independently over 5 ticks | 15 examples, 0 failures |
| `.../sched_service_spec.spl` | 4 examples: ids 0/1/2, per-task priorities, id-0-is-not-a-sentinel, runaway demotion hits one task | 12 examples, 0 failures |
| `.../pm_service/pm_service_spec.spl` | 3 examples: three forks -> pids 2/3/4 + entity ids 1/2/3, exit-one-sibling isolation, pid<->entity round trip | new block 3/3 green |
| `.../wm/wm_world_multi_window_identity_spec.spl` (**new file**) | 5 examples: ids 256/257/258, per-window owner/process/app, grouped counts, despawn-middle, set_identity isolation | 5 examples, 0 failures |

### Pre-existing reds NOT in this bug class (A/B-proven against `git show HEAD:`)
- `pm_service_spec.spl` — 3 failures (`pm_exec ... calls loader`,
  `pm_exit notifies parent via signal_deliver`, `pm_kill ... invokes
  signal_deliver`). HEAD had **8** failures; the fix cleared 5. The remaining 3
  are the *test-local extern stub shadowing* class: the spec declares Simple
  `fn signal_deliver` / `fn loader_exec` stubs plus counters, but
  `pm_service.spl`'s own `extern fn` declarations win, so the counters stay 0.
  Real implementations exist (`os/posix/signal_compat.spl:171`,
  `os/kernel/loader/loader_api.spl:159`) — the same situation the TERM lane
  resolved in `tty_service.spl` by deleting the local extern declaration.
  Left alone: not the two-hop class, and pm's exec/vmm externs need a decision
  about whether unit tests should reach the real kernel loader.
- `wm/wm_service_metadata_spec.spl` (5 failures) and
  `wm/wm_service_focus_resize_identity_security_spec.spl` (5 failures) — byte
  identical before and after the wm_service fix. Failure is
  `semantic: undefined field 'value': cannot access field on value of type 'i64'`,
  a typing defect in the raw-IPC-payload path, unrelated to entity identity.
  This is why the wm regression cover was added at the `WmWorld` level instead.
- `ds_service_spec.spl` cross-import global read: the spec read the module-level
  `var ds_notify_count` directly and always saw 0. Fixed here with a
  `ds_notify_count_value()` accessor (the known cross-import module-global read
  defect); the same accessor shape was used for the two new clock/sched stubs.

### Before/after failure counts (same binary, same specs)
| Spec | HEAD | After |
|------|------|-------|
| ds_service | 9 | 0 |
| devfs_service | 5 | 0 |
| clock_service | 6 | 0 |
| pm_service | 8 | 3 (unrelated class) |
| pipefs / procfs / rs / sched | 1 / 1 / 0 / 1 | 0 / 0 / 0 / 0 |

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

ALREADY-FIXED (interpreter/JIT). Content: `merge_shared_collection_fields` exists at src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975 and is called from the write-back path (:1140), propagating Array/Dict/ByteArray fields callee->caller while keeping scalars/nested structs value-typed. Repro (THREE hops, `self.world.output.bufs.insert("k",5)` inside a `me`), verbatim on the deployed seed:
```
len=1
```
identical under jit and SIMPLE_EXECUTION_MODE=interpreter. The mutation persists; the extract-mutate-writeback workaround is no longer required.
