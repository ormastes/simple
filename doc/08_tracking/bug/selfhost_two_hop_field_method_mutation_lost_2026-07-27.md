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
