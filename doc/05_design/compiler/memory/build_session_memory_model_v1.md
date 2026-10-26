# Build Session Memory Model v1

**Status:** DESIGN — accepted for implementation in packages P0..P6 (below).
**Owner lane:** compiler memory. **Date:** 2026-10-25.
**Baseline (HIR perf lane, s3-wa build.log, 345 modules, single process):**
HIR per module mean 2.88 s, p50 1.71 s, p90 6.7 s, max 18.6 s;
`rt_transient_heap_promote` ~34 % of Stage-3 HIR time; Stage-3 RSS 9–39 GB.

## 1. Problem

The native runtime has no GC. It has one lifetime tool: a **transient scope**
(`rt_transient_array_scope_begin/pause/end`, `runtime_native.c:1690`). Every
object allocated while a scope is active gets `transient_scope_id = S` and is
freed at `scope_end`. Anything that must outlive the scope is **promoted**
(`rt_transient_heap_promote`, `runtime_native.c:2704`, Rust twin
`collections.rs:2182`): the whole reachable graph is walked and every node is
retagged `scope_id = 0` = **permanent until process exit**. Objects allocated
while a scope is *paused* are untracked, i.e. also permanent.

Three consequences, all measured:

1. **O(N²) promote.** `bootstrap_hir_modules_promote_last`
   (`20.hir/hir_lowering/_Items/lowering_helpers.spl:203`) promotes the 7
   process-global registry arrays (`_bootstrap_hir_module_{names,symbols,
   functions,constants,enums,structs,classes}`) once per module. Since
   `e8152c252ad` the walk may not prune at an unowned (scope 0) node, because
   a paused-scope allocation can hold scope-owned children. So module *i*
   walks all *i−1* earlier rows and their items: Σ_i O(i·items) = O(N²).
   `50.mir/_MirLowering/bootstrap_globals.spl:111` does the same for 18 MIR
   arrays. The Rust twin additionally runs `scope.objects.retain(..)` per call
   (`doc/08_tracking/bug/stage3_quadratic_transient_heap_promote_2026-09-02.md`).
2. **Eviction does not lower RSS.** HIR/MIR eviction (#4698 #4705 #4708) drops
   Simple-level references, but promoted graphs are permanent; nothing frees.
3. **No bounded shared storage.** Cache budgets exist only for on-disk/daemon
   caches (#4396 usage ledger, #4405 byte caps, #4506 count budgets,
   `80.driver/cache/metadata/cache_limits.spl`, `cache/gc/admission.spl`).
   In-memory shared data (TLDR surfaces, interned strings, generic views) has
   no count/byte bound and no eviction.

## 2. Model: three lifetimes + one sharing mechanism

| Tier | Owner | Lifetime | Freed by |
|---|---|---|---|
| **T0 Module scope** (exists) | transient scope `M_i` | one module's parse/lower | `scope_end(M_i)` |
| **T1 Build session** (new) | `BuildSession`, heap scope `S` | one build / request | `rt_session_heap_end(S)` — one sweep |
| **T2 Global dataset** (new) | process, `GlobalDataset` | until evicted | LRU/reference-aware eviction → `rt_rc_release` |
| **RC shared** (new) | refcount, no scope | until rc = 0 | `rt_rc_release` reaching 0 |

Promotion becomes **"move to the parent tier"**: T0 → T1 (`adopt`) or
T0/T1 → RC (`share`). `scope_id = 0` is reserved for genuinely immortal data
(string literals, interned builtins) and is no longer produced by promotion.

## 3. Invariants

- **I1 Lifetime monotonicity.** An object never references an object of a
  shorter lifetime (T2/RC ≥ T1 ≥ T0; `scope_id 0` ≥ everything). Publication is
  *promote-then-publish*: a row is adopted into `S` **before** it is appended to
  a session-owned container. (Today's `e8152c252ad` hazard — unowned root with
  owned children — is exactly a violation of I1; the model forbids it instead of
  walking around it.)
- **I2 Prunable walks.** Because of I1, `adopt(v)` stops at any node whose
  `scope_id != active module scope`. Cost of adopting a module's output is
  O(objects allocated by that module), never O(session).
- **I3 Session containers grow under the session allocator.** Appending to a
  session-owned container runs inside `rt_session_alloc_begin/end` so the
  reallocated backing store is tagged `S`, never `M_i`. No promotion of outer
  arrays, ever.
- **I4 One sweep per session.** `rt_session_heap_end(S)` frees every object
  with `scope_id == S` and `rc == 0` in one pass over the per-session object
  list (same mechanism as `rt_core_transient_heap_scope_objects`, one list per
  live scope id). Nothing else is needed to release a build's memory.
- **I5 RC objects are acyclic.** Refcounted structures (surfaces, interned
  strings, generic instance views, dataset entries) form a DAG. No weak refs in
  v1; a debug-only cycle check (`SIMPLE_RC_CYCLE_CHECK=1`) walks a graph at
  `share()` and fails closed on a back-edge. Parent→child edges in these
  structures are the only edges; child→parent pointers are forbidden by review.
- **I6 Layout ABI frozen.** `RtCoreArray/Dict/Enum/Closure/Float/String` field
  offsets do not change (native codegen reads them). The refcount lives in a
  **pointer-keyed side table** with rows only for rc roots (objects passed to
  `rt_rc_share`), as landed by P4 — not a row parallel to the whole pointer
  registry (see the ownership header in `rc_graph.rs`). The 16 spare header bits are not used for rc.
- **I7 Dual implementation.** Every new `rt_*` symbol lands in
  `src/runtime/runtime_native.c` **and** `src/compiler_rust/runtime/src/value/`
  with the same contract and a selfcheck in `src/runtime/test/` plus a Rust
  unit test (`check-rt-dual-implementation-ratchet.shs` row).
- **I8 Bounded global dataset.** `GlobalDataset` never exceeds `max_count`
  entries or `max_bytes` measured bytes; admission is checked before insert
  (same shape as `cache/gc/admission.spl`), eviction is LRU among entries whose
  `rc == 1` (held only by the dataset). Entries with `rc > 1` are pinned and
  are never evicted to meet a target ("never delete a protected root").

## 4. Runtime surface (C + Rust twins)

```
# Session heap (T1)
rt_session_heap_begin() -> u32 S            # 0 on failure; one live session per thread
rt_session_heap_end(S) -> bool              # frees scope_id==S && rc==0 (I4)
rt_session_alloc_begin(S) / rt_session_alloc_end()   # new objects get S (I3)
rt_transient_heap_adopt(v) -> bool          # retag reachable M_i nodes to S, prune per I2
# Refcount (RC / T2)
rt_rc_share(v) -> bool                      # move graph out of scopes: rc=1, scope_id=0-with-rc
rt_rc_retain(v) -> bool / rt_rc_release(v) -> bool   # release to 0 frees graph (children released)
rt_rc_count(v) -> i64
rt_heap_graph_bytes(v) -> i64               # measured size for I8 admission
```

`rt_transient_heap_promote` stays as a compatibility alias for `adopt` when a
session is open (and for the old behaviour when none is), so untouched callers
keep working while packages migrate. Module scopes nest inside the session:
`scope_begin` while `S` is open makes `S` the parent; a paused module scope
allocates into `S`, not into `0`.

Existing `rt_shared_*` (Rust `objects.rs:762`, C stubs `runtime_native.c:16867`)
is a value wrapper, not an object-graph refcount; it is left alone and will be
re-expressed over `rt_rc_*` in a later version.

## 5. Compiler surface

```
class BuildSession:                    # src/compiler/80.driver/session/build_session.spl
    heap: u32                          # S
    hir_store: BootstrapHirStore       # the former 7 globals, one struct
    mir_store: BootstrapMirStore       # the former 18 globals
    surfaces, symbol_tables, diagnostics, caches: session-owned
    me begin() / me end()
    me module_begin(name) / me module_end()          # wraps transient scope
    me publish_hir_row(row) / me publish_mir_rows(...)  # adopt-then-append under alloc(S)
```

`CompileContext` (`driver_types.spl:530`) gains `session: BuildSession`; the
daemon/LSP/test-runner create one session per request and `end()` it. The
public helper names (`bootstrap_hir_modules_add`, `bootstrap_hir_module_count`,
`bootstrap_fn_*`, …) are kept as forwarding functions over the session store so
20.hir / 50.mir / 70.backend callers change only where they *promote*.

`GlobalDataset` (`src/lib/nogc_sync_mut/mem/global_dataset.spl`): keyed by
identity digest; `max_count`, `max_bytes` from `CacheLimits`-style config
(`SIMPLE_GLOBAL_DATASET_MAX_ENTRIES`, `SIMPLE_GLOBAL_DATASET_MAX_BYTES`), LRU
clock, `get(key) -> retain`, `put(key, v)` = `rt_rc_share` + admission + evict.

## 6. Why the O(N²) disappears

Per module *i* today: adopt new row O(items_i) **+** walk 7 outer arrays
O(Σ_{j<i} items_j). Under I1–I3 the second term is gone: the row is adopted
(O(items_i)), then appended under `alloc(S)`; the outer arrays are never walked.
Total O(Σ items) = O(N). The Rust `retain` per call is removed by deferring
compaction to `scope_end` (bug record's option 1), making it O(N) as well.
RSS: a build's memory is freed at `end()`; HIR/MIR eviction now frees because
evicted graphs are `S`-owned, not permanent.

## 7. Migration steps (small, independently landable PRs)

| Pkg | Scope | Files | Gate |
|---|---|---|---|
| **P0** | Rust: defer `retain` to scope end; C+Rust: prune at non-module nodes (I2 pre-step, safe only together with P2's publish order) | `collections.rs`, `runtime_native.c` | selfchecks + stage-2 sanity |
| **P1** | Runtime session heap: `rt_session_heap_*`, `rt_session_alloc_*`, nested scope parent, `adopt` | C + Rust twins, `rt_transient_heap_scope_selfcheck.c`, Rust tests, SFFI decl in `sffi/host.spl` | dual-impl ratchet, selfchecks |
| **P2** | `BuildSession` + `BootstrapHirStore`; replace the 7 HIR globals; `publish_hir_row`; delete `bootstrap_hir_modules_promote_last` | `80.driver/session/`, `lowering_helpers.spl`, `driver_hir_pipeline_lowering.spl`, `driver_types.spl` | HIR specs, stage-3 HIR time + RSS |
| **P3** | `BootstrapMirStore`; replace 18 MIR globals; delete `bootstrap_mir_registries_promote` | `bootstrap_globals.spl`, `mir_data.spl`, `module_lowering.spl` | MIR specs, stage-3 time + RSS |
| **P4** | Refcount: registry meta row, `rt_rc_*`, `rt_heap_graph_bytes`, debug cycle check | C + Rust twins + tests | dual-impl ratchet |
| **P5** | `GlobalDataset` (count+bytes, LRU, pinned-by-rc); wire TLDR surfaces + interned strings | `src/lib/nogc_sync_mut/mem/`, `module_surface_registry.spl` | unit specs, daemon RSS |
| **P6** | Session `end()` in daemon/LSP/test-runner; per-module sub-scope freed after object emit | `80.driver`, `app/mcp`, `app/test_runner_new` | request-loop RSS flat over 100 requests |
|  | **P6 status (landed narrowed):** `BuildSession.end(kept)` + `CompilerDriver.compile()` wiring, fail-closed, **opt-in** (`SIMPLE_BUILD_SESSION_END=1`; default skipped, logged once `build-session: end disabled (opt-in)`). Flip the default after one green s3 run with `SIMPLE_BUILD_SESSION_END=1` (only a natively compiled compiler frees; the interpreter refuses `rt_rc_share`). After end, `build_session_end_reset_globals_v1()` resets HIR/MIR bootstrap stores + aspect/effect/rt_criticality/layer_eq registries. Session-fed globals left dangling after end() (no exported reset; unsafe to read after compile() returns): `resource_registry` (reset not exported), `_bootstrap_fn_*` dicts/journals in `50.mir/mir_data.spl` (only private `_bootstrap_fn_delta_reset`), aspect/effect/layer_field pending scalars are text/bool (reset by their own `*_pending_reset`, not needed). `module_surface_registry` has no module globals (driver-owned); HirLowering phase memos/symbol tables are per-instance (die with the driver); no global frontend parser identity receipt found. No in-process request loop calls `compile()` (daemon/LSP/MCP/test-runner spawn processes), so per-request lifecycle = per-compile begin/end. GlobalDataset surface consumer NOT wired: surfaces are rebuilt per compile and held raw by `streaming_module_surfaces_owner`, no cross-compile reuse exists to acquire/release. Per-module sub-scope release N/A: P2/P3 adopt rows into the session, none is an rc root. | | |

P0 and P1 may land in either order; P2 requires P1; P3 requires P2; P4 is
independent of P1–P3; P5 requires P4; P6 requires P2 and P5.

## 8. Measurement protocol (every package PR)

Report **before/after** on the same binary identity: wall time of the phase
touched (Stage-3 HIR or MIR per-module mean/p50/p90), **peak RSS** of the
compiler process (`/usr/bin/time -v` on Linux; `Get-Process ...
PeakWorkingSet64` sampled by `scripts/perf/measure-peak-rss.shs`, added in P0),
and the spec result line. No PR lands with a regression in any of the three.

## 9. Non-goals / risks

- No tracing GC, no weak refs, no cross-thread sessions in v1 (a session is
  owned by the thread that opened it, like today's scope owner token).
- A caller that still promotes an outer container pays O(N) once; it is a
  review finding, not a crash. `SIMPLE_TRANSIENT_PROMOTE_DEBUG=1` reports it.
- The registry meta row adds 8 bytes per heap object in the side table.

## 10. Landing status (2026-10-25)

All packages landed on `release/1.0.0` the same day: design #4783, P0 #4802,
P1 #4811, P2 #4837, P3 #4841, P4 #4799, P5 #4804, P6 #4842 (plus bug record
#4806). Measured so far (micro-level; the Stage-3 figure is still pending):

| What | Before | After |
|---|---|---|
| Outer-array adopt, N=2000 rows (Rust / C) | 40,335 ms / 24,777 ms (promote) | 92 ms / 52 ms (adopt visits 1 node) |
| Rust promote, address-collision fallback, N=2000 | 2,717 ms | 33 ms |
| MIR store publish bench, 1000 modules x 50 fns (fake port) | 577.2 s, outer arrays walked 1000x | 163.5 s, walked 0x |
| rc share+release, 100k-object graph (C) | 146.6 MB peak (leak) | 21.8 MB peak |

Still on the legacy `promote` alias (full walk, retags to the session):
HIR `hir_module`, diagnostics, phase memos, symbol tables, frontend registries,
module surfaces; MIR owner roots (drafts #4761/#4762) and `_bootstrap_fn_*`
(already delta-only). Moving the growing HIR containers (phase memos, symbol
tables) under the session allocator is the next perf step.

`BuildSession.end()` is OPT-IN (`SIMPLE_BUILD_SESSION_END=1`) until one green
native Stage-3 run; under the interpreter `rt_rc_share` refuses, so `end()` is
always skipped there. Globals still dangling after an `end()`:
none known: `resource_registry` and `mir_data` `_bootstrap_fn_*` are now reset by
`build_session_end_reset_globals_v1` (spec `build_session_end_reset_globals_spec.spl`).
Kill-switches: `SIMPLE_BUILD_SESSION=0` (no session), `SIMPLE_BUILD_SESSION_END=0`.
Next s3 run should record HIR/MIR per-module time and `PeakWorkingSet64`
with and without `SIMPLE_BUILD_SESSION_END=1` (method: HIR perf lane, #4764 body).
