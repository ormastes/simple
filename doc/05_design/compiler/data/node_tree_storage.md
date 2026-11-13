# Node-tree storage for AST / HIR / MIR: measure, then choose per attribute

Status: design (phase B of the node-storage lane, 2026-11-13); phase C library landed
(§7.1), driver adoption C.2 open (§7.2). Plan:
`doc/03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md`
(§3, §5, §6, §8.4, §12.3). Phase A landed the selection surface: the storage
mechanism of every `@node_tree` attribute is chosen by a source tag or an SDN
rule through the one W1 resolver (`direct | column | sparse_hash`), and the
generated view carries `schema_digest` (logical) and `physical_plan_digest`
(mechanism per attribute). This note decides WHAT the mechanisms should be for
the production trees and HOW a frozen tree is shared, from measurement, and
fixes the write-once / async contract the later phases implement.

Default rule for every phase that follows: the CURRENT layout stays the default
per node family until before/after evidence (bytes per node, phase RSS, wall
time within ~2% or a win, value-identical HIR/MIR dumps on a fixture set) says
otherwise. A switch is an SDN rule row, not a code edit.

## 1. Measurements (interpreter lane, Rust seed)

Executing binary (the `simple test` wrapper execs a generation binary):
`src/compiler_rust/target/bootstrap.generations/8ea37491fb8e95ca0467aefd707ed0189260b724f6d9dc8dcee4b9092875b511-d59cc6238831a991b5a02de7640089dede84ccdb40166c1e3f65667640e467bc/simple`
(119,570,696 bytes, 2026-11-05 18:12:30), worktree at `f78d0d7bc9b`, box
shared with a 20-40 GiB census. Probe (committed, perf lane):

```
SIMPLE_PERF_PROBES=1 systemd-run --user --scope -q -p MemoryMax=8G \
  src/compiler_rust/target/bootstrap/simple test \
  test/05_perf/compiler/data/node_storage_footprint_probe_spec.spl      # ~8 min
```

Per module it parses into the flat pools, boxes a `ParserModule` with
`flat_ast_to_module`, lowers with `HirLowering.lower_module`, encodes the HIR
with `hir_module_encode` (one scalar per line, position-independent) and lowers
to MIR. RSS is `memory_usage()` (`/proc` RSS, OS truth) — `rt_heap_live_bytes`
reads a constant here because seed interpreter values live outside the hosted
heap registry. AST nodes = `expr_count() + stmt_count()`; MIR size =
instructions + terminators.

### 1.1 Results

Output of the committed probe (one process, rows in run order; RSS deltas in
bytes between the phase boundaries; `(reuse)` = negative delta, the allocator
recycled memory freed by `reset_all_pools()`):

| module | src lines | AST nodes | HIR fns | HIR blob bytes | MIR insts | Δ pools | Δ bridge | Δ HIR | Δ MIR | bridge B/node | HIR B/node | blob B/node | MIR B/inst |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `00.common/data/data_schema_resolver.spl` | 514 | 1,973 | 27 | 349,431 | 3,223 | (reuse) | 466,944 | 3,575,808 | 18,112,512 | 236 | 1,812 | 177 | 5,619 |
| `20.hir/hir_lowering/attr_access_sites.spl` | 188 | 638 | 12 | 117,314 | 934 | (reuse) | 12,288 | (reuse) | (reuse) | 19 | — | 183 | — |
| `50.mir/mir_lowering_stmts.spl` (cold) | 5,513 | 15,235 | 99 | 2,391,922 | 21,077 | 52,772,864 | 20,008,960 | 23,564,288 | 113,127,424 | 1,313 | 1,546 | 157 | 5,367 |
| `50.mir/mir_lowering_stmts.spl` (repeat) | 5,513 | 15,235 | 99 | 2,391,922 | 21,077 | (reuse) | 1,060,864 | 40,259,584 | 64,720,896 | 69 | 2,642 | 157 | 3,070 |

Supplementary: a scratch split probe (same binary, `reset_all_pools -> parse ->
bridge -> HIR` only, no MIR; three runs of the large module) read bridge
20.5 / 22.7 / 23.2 MB (1,346 / 1,487 / 1,526 B per node) against HIR
28.8 / 44.5 / 46.4 MB, i.e. a bridge share of 42 / 34 / 33 % of bridge+HIR; an
earlier scratch run of the same pipeline read MIR at 2.0-2.2 KB per
instruction, so the MIR figure is allocator-state dependent (2.0-5.6 KB).

Per AST node on the large module: **bridge 1.3-1.5 KB on a cold heap**
(hidden by reuse on repeats: 69 B), **HIR 1.5-2.6 KB of RSS**, **HIR blob
157 B (~33 scalars)**. Cold-row bridge share of the bridge+HIR peak: 46 %
(split probe: 33-42 %).

### 1.2 Reading the numbers

- **RSS on a non-shrinking interpreter heap is an upper bound**; "(reuse)"
  marks rows where the allocator recycled memory freed by `reset_all_pools()`
  (negative deltas). Repeated rows are the per-phase estimate; the cold `pools`
  row (~4.1 KB/node) includes one-time module loading.
- **The allocator-independent metric is the HIR blob: 150-183 B per AST node.**
  A u32 column arena with a span table is a small multiple of 4 B per scalar,
  i.e. under half the text blob and an order of magnitude under the boxed tree
  (~2-3 KB/node). HIR is what a MIR worker must hold per module — the hirres
  lane's 20-25 GiB of promoted HIR across workers is this number times fan-out.
- **The bridge is a peak cost, not a resident one** (cold heap: 20 MB, 1.3 KB per AST node on the 5.5k-line module; invisible on a warm heap). The streaming driver calls
  `ast_reset()` and `self.ctx.modules = {}` right after HIR lowering
  (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1641-1643`); the
  non-streaming path keeps `ctx.modules: Dict<text, ParserModule>`
  (`driver_types.spl:436`). So "every node is paid twice" holds for peak RSS
  during lowering (pools + boxed tree + HIR live together) and for the
  non-streaming path only.
- **MIR counts include runtime-fallback placeholders** (modules are lowered
  without import surfaces; 24 `[mir-lower] WARNING` on the first module);
  ratios hold, absolute MIR sizes are not production figures.
- **Phase C conclusion:** do not rewrite the ~10k lines of HIR lowering that
  consume `Expr`/`Stmt`. Shrink the bridge: box one function's tree at a time
  (`flat_bootstrap_function_at` already converts on demand via
  `convert_decl_fn(decl_idx)`; `flat_bootstrap_body_at` is still a stub
  returning an empty Block), lower it, release it. Expected peak saving ≈ the
  cold-row bridge delta minus one function (~20 MB on a 5.5k-line module, 1.3-1.5 KB
  per AST node), behind a resolver rule with the whole-module bridge as the
  default until the native lane measures it.

### 1.3 What the native lane must measure (quiet box, owner-scheduled)

Interpreter RSS is dominated by boxed `Value`s; the native number decides the
layout. Record both binaries (`readlink -f` + `stat -c '%s %y'`):

```
# per-phase RSS of a real build, before/after a layout switch (same sha, own cache scope)
SIMPLE_CACHE_SCOPE=nodestore-a /usr/bin/time -f 'wall=%e rss_max_kb=%M' \
  bin/simple build native src/app/cli/main.spl 2>&1 | tail -3
# MIR shard workers: total RSS = sum of /proc/<pid>/status VmRSS over the process tree,
# sampled by a PROPOSED gate scripts/check/check-process-tree-rss.shs (NOT present yet) while
# SIMPLE_MIR_SHARDING=1 SIMPLE_MIR_SHARD_INTERFACE_HIR=1 bin/simple build native ...
# value identity: HIR codec blobs and MIR dumps of the fixture set must be byte-identical
bin/simple test test/02_integration/compiler/data/ast_node_pool_pilot_spec.spl
```

## 2. How other compilers store trees (survey)

| Compiler | Node identity | Layout | Payload encoding | Interning | Rare attributes | Lifetime |
|---|---|---|---|---|---|---|
| rustc | `newtype_index!` u32 ids (`HirId`, `DefId`, `Local`, `BasicBlock`); `IndexVec<I, T>` | HIR in a `TypedArena` per crate; MIR `Body` = `IndexVec` of blocks (AoS per block, SoA across locals/decls) | enums with boxed children; `Span` is 8 bytes, large spans interned | `Symbol` (u32), `Ty<'tcx>` interned by pointer identity | side tables keyed by `HirId`/`DefId` (`TypeckResults`, spans, attrs) | query system (memoized, Salsa-like); `Steal<T>` moves MIR between passes; AST dropped after lowering |
| Clang | pointers into `ASTContext` | `BumpPtrAllocator` arena, nodes `new (Context)`; variable-length payload via `TrailingObjects` | `SourceLocation` u32; `QualType` = pointer + qualifier bits; bit-packed `Stmt`/`Decl` headers | `IdentifierTable`; types uniqued in `FoldingSet`s | side maps on `ASTContext` (comments, attrs) | whole-TU arena, freed at TU end |
| LLVM IR | pointers; intrusive `ilist` | `BumpPtrAllocator`, `SmallVector` inline storage | `Use` list, `Value` subclass data bits | `Type`/`Constant`/`MDNode` uniqued in `LLVMContext`, `StringMap` | metadata attachments as side tables | module freed after codegen |
| Swift | pointers into `ASTContext` | permanent + solver arenas; SIL has its own module allocator | `SourceLoc` from a buffer pointer; `TypeBase` bits | `Identifier`; canonical types uniqued | request evaluator caches | request evaluator (Salsa-like) with cycle diagnostics; solver arena freed per expression |
| Zig | `Node.Index`/`Inst.Index` u32 | `MultiArrayList` SoA (tags, main_token, data), `extra_data: []u32` for variable payloads | ZIR/AIR `Inst` = 1-byte tag + 8-byte data, overflow in `extra` | `string_bytes`, `InternPool` for types/values | per-decl side tables | ZIR per declaration, freed after Sema; incremental dependency graph |

What is common: 32-bit indices instead of pointers (position independent,
half the size, trivially serialisable); contiguous arenas per phase, freed as
a unit; tag + small fixed payload with an `extra` array for the long tail;
interned strings/types compared by id; rare facts in side tables keyed by node
id; later-phase results computed by memoised queries that never mutate the
frozen tree. What differs is AoS vs SoA, and every one of them chose it per
hot/cold access pattern, not globally.

## 3. Target shape for Simple's trees

Starting point: the production AST is already flat SoA pools indexed by `i64`
node id (`_AstExpr/nodes.spl`, `FlatPoolState`), bridged into a boxed
`ParserModule` for HIR lowering (§1.2); HIR and MIR are boxed enum trees with a
position-independent line-blob codec decoded per module (`hir_cache_load`), so
every MIR worker holds its own copy; the `@node_tree` view already selects
`direct | column | sparse_hash` per attribute (Phase A).

Target, per phase, each step behind the resolver with the current layout as the
default until measured:

1. Node ids are `i64` today and stay the public type; the arena may store them
   as u32 slots (plan §5: identity is separate from physical ordinal). Spans
   become one u32 index into a span table (the AST already has
   `span_pool_*`), not four i64 fields per node.
2. Hot attributes (tag, span, left/right, type id) are `column`s of the family
   arena; cold/rare attributes (doc comment, attributes, inferred type,
   diagnostics, generic instantiation lists) are `sparse_hash` side tables.
   Which is which is decided by the access census the attr-access side table
   already records (`attr_access_sites.spl`, W2b), not by taste.
3. Variable-length payloads (args, stmts, type args) live in one `extra: [i64]`
   array per family with (offset, len) in the node, Zig-style, instead of
   `[[i64]]` arrays of arrays.
4. Strings are interned once per build session (`sym_names`, literals) and
   nodes carry the id.
5. A module's frozen tree is one contiguous, position-independent blob
   (columns + extra + string table + header with `schema_digest` and
   `physical_plan_digest`), so sharing it is mapping it (§5).
6. Per-phase lifetime: the AST arena of a module is released when its HIR cell
   is published; HIR bodies when the owning MIR module's cell is published
   (the hirres lane's interface-only projection is the first instance of this
   rule).

## 4. Write-once (pseudo-immutable) contract

- Construction is an internal, single-owner obligation (`NotInit`,
  `node_construction_*_v1` in `node_lifecycle_contracts.spl`): a node and each
  attribute are initialised exactly once inside the producer, with zero
  synchronisation, and the builder never escapes to readers.
- After `finish` the tree is frozen: the generated view has getters only; the
  generated stores' `set` exists on the builder side of the phase and a
  post-freeze write is a compile-time error in generated code (no setter is
  emitted on the frozen view) and fails closed at runtime for the stores (the
  phase cell refuses a second publish).
- Later-phase results (inferred types, resolved symbols, layouts, diagnostics)
  go into separate write-once side tables keyed by node id (plan §4.4), each
  its own cell, never by mutating the frozen node.

## 5. Async surface: one write-once cell per (phase, module)

Landed as the deterministic model in `node_lifecycle_contracts.spl`
(`PhaseCellTableV1`, `phase_cell_{declare,publish,fail,await}_v1`, spec
`test/01_unit/compiler/data/node_lifecycle_contracts_spec.spl`):

- `publish` succeeds once and releases waiters in registration order; a second
  publish or a late `fail` is refused and the first value stays.
- `await` never answers "not initialised": `Pending -> Waiting`,
  `Published -> Ready(value)`, `Failed -> ProducerFailed(reason)`; a reader that
  arrives after publication reads the same frozen value as one that waited.
- A wait that would close a cycle is refused BEFORE registration with
  `await cycle: hir:c -> hir:a -> hir:b -> hir:c`; a self-await is the shortest
  cycle. The runtime binding must keep this order (check, then CAS-register).
- A failed producer releases its waiters with the failure: dependents are
  excluded (go-to-end), never blocked.
- Granularity is the module per phase (`await hir(module)`); inside a frozen
  module every read is a plain indexed load. Per-attribute cells only for rare
  lazily computed attributes stored in sparse side tables; never a future per
  hot node attribute.
- Determinism: outcomes depend only on cell state, so output cannot depend on
  completion order; the cell value is the blob digest, which makes "same input,
  same tree" checkable across workers.

Runtime binding (phase D): one word per cell (`AtomicI64` state, CAS
`Pending -> Published|Failed`, `std.nogc_async_immut.atom.cas`), a parked
waiter list appended by CAS, the blob published to the session heap
(`build_session_memory_model_v1.md` tier T1/RC) before the state flips
(promote-then-publish, invariant I1).

## 6. Sharing a frozen module across workers (integration point)

Today each MIR shard worker (`driver_build/native_mir_shard.spl`) re-runs the
front half, decodes every HIR module from the cache and promotes it; the
hirres lane (landed in #8808,
`driver_mir_shard_hir_residency_v1.spl`) cuts that to an interface-only
projection per non-owned module at `hir_cache_load_in_owned_scope(key, ...,
interface_only)` and reloads a claimed module's body after the claim. The
frozen-blob design plugs into exactly that seam and composes with it:

- `hir_cache_load_in_owned_scope` gains a third answer besides "decode full"
  and "decode interface": "map the frozen blob read-only" (mmap of the
  per-module blob file under `native_cache/<scope>/hir/`, or the parent's
  session-heap page range inherited copy-on-write by forked workers). N
  workers then read ONE physical copy instead of N promoted trees.
- The post-claim body reload becomes "take the body columns from the same
  mapping"; nothing is decoded twice.
- Completion is published through the module's phase cell with the blob digest
  as value, so a worker that needs module B's HIR awaits `hir:B` instead of
  polling the ledger; cycles across modules surface as the diagnostic in §5.
- The hirres lane owns residency policy (which modules a worker holds); this
  lane owns the storage/arena layer (what a held module costs and how it is
  mapped). Neither touches the other's files; the shared surface is the
  loader signature above and the cell key `hir:<module>`.

## 7. Phase plan and acceptance

| Phase | Change | Evidence before the default flips |
|---|---|---|
| C (AST) | per-module compact pool snapshot (packed `.spab` bytes in memory) behind a write-once `ast:<module>` cell; `ParserModule` materialised from it right before lowering; selected by the `compiler.ast` rule (§7.1); driver adoption is C.2 (§7.2) | bytes/node and parse+HIR RSS on the §1 module set; HIR codec blobs identical to the cache-hit restore (not the fresh parse, see §7.1); wall time within 2% |
| D (HIR) | module blob arena + phase cells + mapped read-only sharing at the hirres seam | per-worker and total RSS with K shard workers; identical MIR dumps |
| E (MIR) | `MirInst` columns + `extra` array; same cells | object-file identity on a fixture set; lowering wall time |

Each phase lands behind a resolver rule with the current layout as default,
runs the compiler unit specs of the touched layer, and never requires a
native build on the census box; native measurements are scheduled by the
coordinator with the commands in §1.3.

### 7.1 Phase C as landed (2026-11-13): AST pool snapshot

Relation to §1.2: §1.2 proposed a per-function bridge. Phase C instead keeps the
whole module's AST in its compact column form between parse and lowering and
materialises the boxed tree once, at the lowering seam; the per-function bridge
remains a later refinement inside materialisation and is not contradicted.

Code: `src/compiler/10.frontend/snapshot/ast_pool_snapshot_v1.spl`. Spec:
`test/02_integration/compiler/data/ast_pool_snapshot_spec.spl` (5/5).

- **Snapshot** = the packed position-independent `.spab` blob
  (`flat_pool_packed_v1.spl`) of the module's flat pools, captured right after
  the parse (`flat_pool_capture_*`), held in memory (`AstPoolSnapshotV1.bytes`),
  plus the exact parse source and its xxh3-128 key. No new encoding.
- **Materialise** = validate the view, check the published body digest and the
  source key, restore the pools from the typed tokens and run the bridge
  (`build_module_from_packed_view_v1`). Every doubt is an `Err`, never an empty
  module. A materialised module stays valid after another module is
  materialised (spec: self-contained example).
- **Write-once** = `ast_snapshot_store_publish_v1` declares/publishes the cell
  `ast:<module>` (`phase_cell_*_v1`) with the sha256 body digest as value; a
  second publish is refused and the first snapshot stays; a consumer
  (`hir:<module>`) awaits the cell and reads `Ready(digest)`.
- **Selection** = `data_attr_storage_resolve_v1("compiler.ast",
  "compiler.ast.Module", "nodes", rules, "direct")`: `direct` (the versioned
  default) = boxed tree, `column` = pool snapshot, any other token is an error
  naming it. Recommended key: `site: "compiler.ast.Module.nodes"` (a
  `module: "compiler.ast"` row would also drive every per-attribute choice of
  the generated AST views). **Default stays `direct`; no flip is proposed.**
- **Equality oracle**: the materialised module lowers to a HIR codec blob
  byte-identical to the production cache-hit restore of the same parse
  (`build_module_from_flat_pool_blob`, and the packed hit is identical to that).
  It is NOT identical to the fresh in-process boxed tree: on
  `attr_access_sites.spl` 2,706 of 25,718 codec lines differ, all span offsets
  that the fresh bridge gets wrong and every cache hit gets right — a
  pre-existing cold/warm divergence filed as
  `doc/08_tracking/bug/fresh_parse_vs_cache_hit_span_divergence_2026-11-13.md`.

Measurements (same seed binary as §1:
`.../bootstrap.generations/8ea37491...e467bc/simple`, 119,570,696 bytes,
2026-11-05 18:12:30; `simple test` lane under `MemoryMax=8G`, shared box,
load ~8; one run of the spec, `SNAPSHOT` lines):

| module | AST nodes | snapshot bytes | B/node | parse+bridge µs | encode µs | materialise µs |
|---|---|---|---|---|---|---|
| `20.hir/hir_lowering/attr_access_sites.spl` | 638 | 125,200 | 196 | 2,345,106 | 5,521,531 | 3,726,909 |
| `lib/common/text_bytes.spl` | 198 | 51,664 | 260 | 3,631,250 | 2,213,935 | 3,833,567 |
| `00.common/data/data_schema_resolver.spl` | 1,973 | 342,736 | 173 | 10,594,790 | 15,187,931 | 103,769,537 |

Before/after, like for like on `data_schema_resolver.spl`: boxed bridge 236 B
per node on a reused heap (§1.1 row) and 1.3-1.5 KB per node on a cold heap
(§1.1 large-module row) versus 173 B per node packed — about 27 % smaller warm,
7-8x smaller cold. The brief's "about 76 B per node" figure does not appear in
this note's measurements; the measured packed snapshot is 173-260 B per node
(small modules pay the fixed header and string table).

Time: on this interpreter lane materialising costs ~10x the parse it replaces
on the 514-line module (104 s vs 10.6 s); the cost is the pre-existing pool
restore + bridge (the `.fpc` line-cache hit costs the same, 95 s; view
validation is 2.7 s), filed as
`doc/08_tracking/bug/flat_pool_restore_10x_slower_than_parse_interpreter_2026-11-13.md`.
**The interpreter lane shows a time regression, not a win**; the native lane
(where `.spab` is the default hit format) must be measured before any default
changes.

### 7.2 Phase C.2 (open): driver adoption

Blocked on the restore-cost bug above and a native-lane RSS measurement
(§1.3). The exact seam, so the change is mechanical once unblocked:

- **Producer**: `parse_full_frontend_preprocessed_with_scope`
  (`src/compiler/10.frontend/frontend.spl`) miss path, where the pool capture
  already happens for the cache store: encode once, share the bytes between the
  `.spab` store and `ast_snapshot_store_publish_v1`; on a `.spab` hit the bytes
  are the file already mapped. A `.fpc` line hit carries no trace and keeps the
  boxed tree (counted, logged).
- **Retention**: under `column`, `ctx.modules[name]` keeps a body-less module
  (headers/surfaces only) and the snapshot holds the bodies.
- **Consumer**: a branch ahead of `unstub_cached` in
  `driver_hir_pipeline_lowering.spl` materialises from the snapshot, lowers and
  drops the boxed tree. It must sit BEFORE the `ctx.modules[name] != nil`
  check, or a missing module silently falls through to `unstub_reparse` (a
  green build that reparses everything).
- **Reader audit** (must work on a body-less module or route through one
  materialising accessor, with the materialisation count asserted):
  `module_surfaces_from_modules` (`20.hir/hir_lowering/module_surface_registry.spl`),
  `driver_orchestration.spl:110`, the export-facade check in
  `driver_aot_native_output.spl`, and the three `Dict` copies in
  `driver_source_parse_retained.spl`.

## 8. Non-goals and risks

- No per-node futures, no locks (repo rule: immutable values, CAS, messages).
- No `nil`/`any` widening in safe code; absent attribute = `Err`, never zero.
- The seed `run` lane cannot parse the pilot SDN
  (`doc/08_tracking/bug/seed_run_lane_sdn_quoted_scalar_parse_2026-11-13.md`);
  regeneration goes through `simple test` until fixed.
- Interpreter-lane numbers over-state bytes per node; they rank the phases and
  attributes, the native lane confirms the absolute savings.
