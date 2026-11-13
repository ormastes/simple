# Node-tree storage for AST / HIR / MIR: measure, then choose per attribute

Status: design (phase B of the node-storage lane, 2026-11-13). Plan:
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
`/home/yoon/dev/simple/src/compiler_rust/target/bootstrap.generations/8ea37491fb8e95ca0467aefd707ed0189260b724f6d9dc8dcee4b9092875b511-d59cc6238831a991b5a02de7640089dede84ccdb40166c1e3f65667640e467bc/simple`
(119,570,696 bytes, 2026-11-05 18:12:30), worktree at `f78d0d7bc9b`, box
shared with a 20-40 GiB census. Probe (committed, perf lane):

```
cd <worktree> && systemd-run --user --scope -q -p MemoryMax=8G \
  /home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple test \
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

| module | src lines | AST nodes | HIR fns | HIR blob bytes / lines | MIR insts | RSS Δ pools | RSS Δ bridge | RSS Δ HIR | RSS Δ MIR |
|---|---|---|---|---|---|---|---|---|---|
| `data_schema_resolver.spl` | 514 | 1,973 | 27 | 349,431 / 74,042 | 3,223 | (reuse) | +1.56 MB | +3.94 MB | +8.93 MB |
| `data_schema_resolver.spl` (repeat) | 514 | 1,973 | 27 | same | 3,223 | (reuse) | +1.39 MB | +4.00 MB | — |
| `hir_lowering/attr_access_sites.spl` | 188 | 638 | 12 | 117,314 / 25,717 | 934 | (reuse) | — | 0 | (reuse) |
| `mir_lowering_stmts.spl` (cold) | 5,513 | 15,235 | 99 | 2,390,144 / 511,708 | 21,073 | +63.07 MB | +20.52 MB | +28.77 MB | +41.75 MB |
| `mir_lowering_stmts.spl` (repeat ×2) | 5,513 | 15,235 | 99 | same | 21,073 | +19.0 MB / (reuse) | +22.66 / +23.25 MB | +44.54 / +46.40 MB | +45.72 MB |

Per AST node (large module, repeats): bridge **1.35-1.53 KB**, HIR
**1.9-3.0 KB**, HIR blob **156 B (~33 scalars)**; per MIR instruction (the committed probe, which keeps the bridge alive through MIR, read 3.1-5.6 KB)
2.0-2.2 KB. Bridge share of the bridge+HIR peak: 26-42% (33% median).

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
- **The bridge is a peak cost, not a resident one.** The streaming driver calls
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
  bridge column minus one function (~20 MB on a 5.5k-line module, 1.3-1.5 KB
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
hirres lane (`/home/yoon/dev/simple-hirres-20261113`,
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
| C (AST) | HIR lowering reads `FlatPoolState`/expr pools through the generated view instead of `flat_ast_to_module`'s boxed `ParserModule`; the bridge shrinks to the pieces lowering still needs | bytes/node and parse+HIR RSS on the §1 module set; identical HIR codec blobs for the fixture set; wall time within 2% |
| D (HIR) | module blob arena + phase cells + mapped read-only sharing at the hirres seam | per-worker and total RSS with K shard workers; identical MIR dumps |
| E (MIR) | `MirInst` columns + `extra` array; same cells | object-file identity on a fixture set; lowering wall time |

Each phase lands behind a resolver rule with the current layout as default,
runs the compiler unit specs of the touched layer, and never requires a
native build on the census box; native measurements are scheduled by the
coordinator with the commands in §1.3.

## 8. Non-goals and risks

- No per-node futures, no locks (repo rule: immutable values, CAS, messages).
- No `nil`/`any` widening in safe code; absent attribute = `Err`, never zero.
- The seed `run` lane cannot parse the pilot SDN
  (`doc/08_tracking/bug/seed_run_lane_sdn_quoted_scalar_parse_2026-11-13.md`);
  regeneration goes through `simple test` until fixed.
- Interpreter-lane numbers over-state bytes per node; they rank the phases and
  attributes, the native lane confirms the absolute savings.
