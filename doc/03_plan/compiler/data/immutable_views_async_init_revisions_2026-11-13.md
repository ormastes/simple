# Simple: Immutable Views, Async Initialization, Revisions, and Profile-Guided Node Attributes

**Status:** Final architecture and implementation plan (proposal; not a claim of completed implementation)
**Date:** 2026-11-13
**Primary scope:** Simple compiler/interpreter, AST/HIR/MIR, parser-based tools, LSP, generated attribute access, collections, build/cache infrastructure
**Repository destination:** `doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md`
**Program:** sub-plan of the accepted [unified data attributes program](data_attributes_layout_containers_xray_2026-11-06.md) (W0–W10); tracked in [`doc/08_tracking/data_attributes_program_progress_2026-11-07.md`](../../../08_tracking/data_attributes_program_progress_2026-11-07.md)
**Source pin for the integration note below:** `origin/release/1.0.0` @ `9100f50e680`

## 0a. Program integration note (added 2026-11-13; sections 0–14 below are the user-supplied plan, kept verbatim)

**Authority.** This document is the *semantic contract* for the three read-only
handle kinds (`Immutable<T>` / `RevisionImmutable<T>` / `FrozenImmutable<T>`),
for `@support_async_immutable` async initialization, and for the strict
public-field definite-initialization diagnostics. The W-plan remains the
*program*: it wins on storage backends, policy resolution, layout, collections
and XRay. There is one program; the phases below are mapped onto its packages
rather than scheduled beside them.

### Phase → work-package map

| This plan | W-package | Already exists at the pin (do not duplicate) | Owner lane |
|---|---|---|---|
| P0 inventory / non-duplication gate | W0 recheck + W-plan §2.1 audit | §2.1 rows R02–R18; `src/compiler/00.common/data/` resolver v1–v3 (13 modules, #7220); `attr_access_sites.spl` (`HirAttrAccessV1` side table, `5a48dc6d48c`/`eab5f542b48`); `node_lifecycle_contracts.spl` construction facts (`node_construction_*_v1`, #7448) | this lane (immview); deliverable is the symbol-to-requirement map in `doc/08_tracking/` |
| P1 shared attribute semantics + public initialization checks | **W2b enforcement half** (tracker: "V1 facts landed; no compiler/runtime enforcement proof") + W1b effective-visibility binding | W-plan §4.1–4.3 already specify "compile-time error when known … a migration-only warning mode must be explicit and temporary" — that *is* P1's feature gate; §4.2 "no implicit numeric-zero, empty-string, nil … default" is the nil/None rule of §3.2 here | this lane. New verifier module *consumes* `node_construction_*_v1` facts; it does **not** edit `node_lifecycle_contracts.spl` (nodestore lane owns that file) |
| P2 `Immutable<T>` live read-only projection | **new W2c — read-only capability projection** (only item with no prior home) | ownership/borrow rules of the existing type checker; W-plan §5.4 ownership and transfer | this lane |
| P2 `RevisionImmutable<T>` / `FrozenImmutable<T>` | W8 (frozen plans, semantic/physical invalidation, LSP adoption) + W-plan §13.1/§13.3 (pointer-free persistence) | `FileAstV1` pointer-free codec (§2.1 R03); HIR codec v17 (#8808/#8827, interface-only HIR) | this lane for the handle semantics; W8 owners for cache identity |
| P3 async registered initialization | W2b §4.4 ("versioned write-once result sidecar … existing async resource/result mechanisms") | **`phase_cell_*_v1` write-once cells** in the nodestore lane's `node_lifecycle_contracts.spl` @ `f8db9920671` (landed on `release/1.0.0` via #8829, `04f02062860`): `PhaseCellStateV1`, `PhaseCellTableV1`, `PhaseAwaitOutcomeV1`, `phase_cell_table_new_v1`, `phase_cell_declare_v1`, `phase_cell_publish_v1`, `phase_cell_fail_v1`, `phase_cell_await_v1` (cycle diagnostic + failure propagation). P3 builds its per-`(arena, generation, node, attr)` gate on this API by name; it must not add a second once-only state machine | this lane, **depends on nodestore lane landing** |
| P4 storage backend unification | W3b | W3 pilot (`9b27558ef06`), `@attr_storage direct\|column\|sparse_hash` + `data_policy_resolve_rules_v1` + `physical_plan_digest` in the nodestore lane (`bb9cba2d6b4`, `fa0971c8594`, unlanded) | **nodestore lane** |
| P5 static profile-guided selection | W5b / W6 / W7 | `.sprof` v2 envelope, `sprof_collection_profile.spl`, `TraceObserverV1`; W4 `collection_policy_adapter` / `AdaptiveMap` | **nodestore lane** (selection) + W5 owners (observation) |
| P6 opt-in runtime container switching | W9 (deferred behind W6 evidence) | `AdaptiveMap`/`AdaptiveSet` conversion code (§2.1 R09); §11.3 transactional migration | W9 owner; not scheduled by this plan |
| P7 integration, proofs, release | W8 + W-plan §15 | — | program |

### Acceptance-ID ownership

IMM-01..04, ASY-01..08, ATTR-01, ATTR-04 → this lane (P1–P3). ATTR-02/03/05,
PROF-01, PERF-02 → nodestore lane (P4/P5). REV-01/02 → W8. PROF-02/03 → W9.
PERF-01 → program gate before any default flip. §10's IDs are additive to the
W-plan's ATTR-/COL-/XR-/LAY-/RUN-/CACHE-/MIG- series; where §10 reuses the
`ATTR-` prefix with a different number (e.g. ATTR-01 here = "same name,
conflicting tree types" vs. W-plan ATTR-01..06 resolver cases) the spec file
names carry the plan date to keep them distinct.

### P1 landing rule (binding)

P1 introduces a new compile error class. Before any default-on landing the
verifier runs as a **report** over `src/compiler`, `src/lib`, `src/app`; a
non-zero census of existing offenders means the bootstrap (Stage 2/3 compiles
the compiler) would break, so the check lands behind a per-module opt-in /
warning gate with the census recorded, exactly the "explicit and temporary
migration-only warning mode" of W-plan §4.3. New-code semantics remain errors.

### P1 census and gate (recorded 2026-11-13)

**Gate.** It landed in #8860 (verifier `988f8ff6755`, spread fix and gate
specs `265b8f42fb3`). The P2 review follow-ups landed in #8881 (`eb66cc8e5ed`).
`SIMPLE_REQUIRED_INIT_CHECK` = `off` (default) | `warning` | `error`; any
other value is `off`. It is read once per process; specs re-read it with
`required_init_check_mode_reload_v1()`. `off` adds nothing, so Stage 2/3
still compile the offenders below. `warning` records
`LoweringErrorKind.Recovered` rows, the §4.3 migration mode. `error` is the
target semantics. A module can opt in with `@required_init(error|warning)`:
the marker `__module_required_init_<mode>` sets
`ParserModule.required_init_mode`, on the `@no_gc(strict)` model, and the
stricter of module and process mode wins. Per class,
`@support_async_immutable` makes `E_ASYNC_INIT_*` an error in every mode. The
gate is part of the HIR cache identity (`_hir_cache_env_switches`, only when
not `off`), not the managed-parse identity.

**Census method.** `scripts/check/census_required_field_init_spec.spl` is a
report-only harness. It runs the verifier standalone on each file
(`parse_full_frontend` + `HirLowering.lower_module`) under the seed runner,
with a 4G cgroup and one process at a time. A textual prefilter keeps the
files that both declare a `struct`/`class` and name one of those types in a
construction (`Name(`, `Name<`, `Name {`, `Self(`). That leaves 6,499 of
15,546 `.spl` files: compiler 1,291, lib 3,509, app 1,699. The prefilter
missed 0 of the 109 judged files among the first 200 files, which were run
unfiltered. Cost is ~5–20 s per file. The runner kills a spec after 900 s,
so chunks hold 25 files. The verifier was pinned at `2ad3be3f250` (the lane
tip before #8860; same verifier as `265b8f42fb3`), so P2 item 2's
named/positional mapping fix is not reflected. A site that mixes positional
and named arguments may be over-counted.

**Figures (final for these scopes, 19:19 KST).**

| Scope | Files censused | Rows | Sites | Classes |
|---|---|---|---|---|
| `src/compiler`, every prefiltered candidate | 1,291 of 1,291 (4 parse-failed) | 146 | 58 | 26 |
| `src/lib`, seeded random 200 of 3,509 candidates | 200 | 1 | 1 | 1 |
| `src/app`, seeded random 200 of 1,699 candidates | 200 | 0 | 0 | 0 |
| everything censused (incl. 35 extra lib files) | 1,816 | 149 | 61 | 29 |

All 149 rows are `E_ATTR_REQUIRED_UNINIT`. No `@support_async_immutable`
class exists yet, so there are no `E_ASYNC_INIT_*` rows. 130 rows come from
one pattern: a `# DESUGARED` optional pair (`has_<f>: bool` + `<f>: T`) left
out of the construction, so the run relies on zero-fill. Largest are
`TypeInfo` (`99.loader/loader/compiler_sffi.spl`, 31), `BorrowError`
(`55.borrow/borrow_check/borrow_graph.spl`, 18), `LifetimeConstraint`
(`55.borrow/borrow_check/lifetime.spl`, 12), `HygieneScope` (9) and
`MacroContractResult` (8). The other 19 rows are 9 classes that omit plain
fields:
- `LlvmBackend` (8)
- `BlockBuilder` private `_completer`/`_highlighter`/`_hover` (3)
- `TensorSuffix` (2)
- `MaybeUninit.value` (`src/lib/nogc_sync_mut/unsafe/maybe_uninit.spl`)
- the two `DataLoaderIterator.done` rows (`src/lib/gc_async_mut/pure/data/dataloader.spl`)
- `JitExecutionEngine`
- `LoaderInstantiationRecord`
- `ThreePayloadObjectReadEvidenceV1`

The lib/app rate is about 1 row per 400 candidate files, against 146 in the
1,291 compiler files: the debt is concentrated in compiler `# DESUGARED`
code. The census is non-zero, so the default stays `off`. Migration
candidates are the DESUGARED optional pairs, which want a real `T?` or field
defaults, and `@required_init(warning)` per module.

**Verifier false positive found and fixed.** The first chunk reported 6 rows
at `00.common/cache_contract/aspect_match_shard_v1.spl:190`. That site is a
struct update `T(..f, facts_key: …)`. The spread arrives as
`Range(None, Some(base))` and was being counted as a positional argument.
The fix (`265b8f42fb3`) uses MIR's `struct_construct_spread_base` shape, and
those rows are excluded above.

**Limits.**
- Standalone lowering does not resolve imports. A construction of an
  imported type therefore has no symbol: it is neither judged nor counted, so
  `sites_unjudged = 0` under-states cross-module sites.
- Imported layouts also carry `has_default = false`.
- The census covers same-module constructions only.
- lib and app are sampled, not exhaustive. The runner continues over the
  rest serially.

### Grammar status

Every code block in sections 2–3 is **unverified syntax** until the P0 probes
record what the parser accepts today (`Immutable<T>` types,
`@support_async_immutable`, `async <expr>` as a constructor argument,
`await x.field`). The library-level `AsyncInit<T>`/`InitProducer<T>` fallback of
§3.1 is the default assumption until a probe proves otherwise.

### Lane assignment (2026-11-14)

Owner direction 2026-11-14: complete this plan together with the node-attribute
program, SPipe + TDD, Windows and pure Simple first. Assignments only; state is
tracked in the progress file's "Owner goal and lane assignment (2026-11-14)".

| Phase | Lane / branch | Order and limits |
|---|---|---|
| P2 `Immutable<T>` (IMM-01/02) | immview, `work/immutable-views-async-init-2-20261114` | First. Real grammar and type support, not lenience; a write through the projection is a named compile error. The seed must accept the syntax; a seed change is reported, not rebuilt by the lane |
| P3 async registered init (ASY-01/02/06/07/08) | immview | Second. On `phase_cell_*_v1` by name; includes parsing `async <expr>` as a constructor argument |
| P2 `RevisionImmutable<T>` / `FrozenImmutable<T>` (IMM-03/04) | immview | Third. Handle semantics only; REV-01/02 cache identity stays with W8 and the missing hook is named |
| P1 census re-run | immview | The 2026-11-13 figures predate the named/positional mapping fix; re-run for `src/compiler`. The gate default stays `off` |
| P4 storage backend unification | nodeattr, `work/node-attr-storage-20261114` | One `AttributeSchema`; array <-> hash switch by tag or SDN rule; default off |
| P5 static profile-guided selection (PROF-01) | tracesel, `work/trace-layer-feature-select-20261114` | After the layer/feature trace fold |
| P6 opt-in runtime switching (PROF-02/03) | tracesel | Opt-in path only, default off. Previously "not scheduled by this plan"; scheduled by the owner direction above |
| P7 | program | Includes the default-on rule: phase 3 must complete with managed storage enabled before any default flip |


## 0. Executive decision

Choose **one typed attribute schema** with **three physical storage families** and **three distinct read-only contracts**. Extend the existing parser, node, ownership, collection, and diagnostic facilities; do **not** create a parallel AST/HIR/MIR node hierarchy or a second generic-attribute system.

1. `Immutable<T>` is a **live, read-only view**. Writes through it are forbidden, but a separate mutable alias may change the underlying object. It does **not** imply a stable snapshot, synchronization, or deep freezing of the backing allocation.
2. `RevisionImmutable<T>` pins one logically consistent revision. Mutable writers create/change a newer revision with COW, a persistent overlay, or ownership-based in-place update when the previous revision is unobservable.
3. `FrozenImmutable<T>` denotes permanently immutable content, produced by ownership consumption or detached copy. It is suitable for shared compiler images, read-only mmap, deterministic hashes, SCV and remote cache payloads.
4. `@support_async_immutable` permits asynchronous **initialization** of explicitly registered missing fields. **Any public field missing both a synchronous value and a valid async producer is a compile error.** The annotation is not a default value and does not hide omissions.
5. Node attribute storage can be **embedded (AoS)**, **indexed column/array (SoA)**, or **sparse pooled hashmap**. All three use the same `AttributeSchema` and generated accessor contracts.
6. Profile-driven **static** selection is the default for compiler hot paths and frozen artifacts. Optional **runtime** switching applies to mutable containers/arenas; migration must be version-safe, hysteretic, and observationally invisible.
7. **AST records syntax; HIR resolves attribute semantics; canonical MIR expresses typed operations; target/layout lowering specializes operations.** Do not expose layout offsets or hashmap implementation details in source-level HIR.
8. Preserve the default fused Parse -> HIR -> MIR -> OBJ pipeline. Do not add a heap-allocated future, lock, hashmap, or virtual getter to every node.

### Decision matrix

| Candidate | Benefit | Defect | Choice |
|---|---|---|---|
| Always embed attributes | Fastest known fields | Sparse fields bloat every node | Supported for hot/dense fields |
| Always use a node-local hashmap | Uniform dynamic API | Lookup/allocation overhead; poor cache locality | Reject as default |
| Universal persistent structure | Easy snapshots | High mutation and compile costs | Use only where needed |
| Hybrid typed schema + backends | Low-cost hot path and sparse flexibility | Needs schema/layout lowering | **Adopt** |
| Runtime auto-switch everywhere | Adapts to changing workload | Indirection, migration and race complexity | **Opt in** at container/arena granularity |

## 1. Evidence, compatibility, and audit boundary

Precedents: Kotlin read-only interfaces / OpenJDK unmodifiable views (read-only != immutable backing); Roslyn red/green trees, rust-analyzer/Rowan, Tree-sitter (structural sharing, versioned parsing); Rust OnceLock, IVar/LVar (single assignment, deterministic parallelism); Salsa (input/tracked/interned identity, revision invalidation); MLIR properties vs attribute dictionaries; LLVM container guidance; Redis compact hash with threshold conversion; Linux RCU.

The exact AST/HIR/node-attribute implementation was NOT audited by the plan author. All integration paths require read-only symbol-level confirmation before editing. Avoid duplicate implementations.

Preserve earlier Simple design constraints: typed `NodeId`/`RegionId`/`ObjId`; `NotInit<Node>` for whole-node construction where already supported; per-tree same-name/same-type attributes; generated virtual get/set; AoS/SoA collection configuration; XRay/profile hooks; strong typing and explicit public visibility; immutable AST/HIR/MIR/OBJ artifact chains; stable async TLDR keys with resolution state external; canonical target-neutral HIR and one canonical MIR; cache codecs that omit runtime pointers and async handles; xxh3 internal identity plus stronger hashes where trust boundaries require it.

## 2. Semantic contracts

| Capability | Write through this handle | Observe later external writes | Stable content while held | Runtime requirements |
|---|---:|---:|---:|---|
| Mutable `T`, `&mut T` | Yes, with ownership/borrow authority | Yes | No | Existing alias/race rules |
| `Immutable<T>` | **No** | **Yes** | **No** | External synchronization for concurrent mutation |
| `RevisionImmutable<T>` | No | No; pinned to one revision | **Yes** | Revision lease/COW/versioned overlay |
| `FrozenImmutable<T>` | No | No | **Yes, permanently** | Unique-consumption proof or detached copy |

`Immutable<T>` applies read-only projection **transitively** along members reached through that handle: a method or child reference may not turn it into an illicit mutable write. Other independently held mutable aliases remain allowed. `Immutable<T>` is not a concurrency primitive.

Do **not** make all `Immutable<T>` handles revision-pinned by default. Define explicit aliases such as `AstSnapshot = RevisionImmutable<Ast>` for compiler APIs. Keep `RevisionImmutable<T>` pinned; expose `latest()`/`follow_latest()` on a separate document/container owner, not on the pinned handle.

`FrozenImmutable<T>` creation rules:
1. If uniquely owned with no unsafe mutable aliases, **consume** ownership and freeze without copying where possible.
2. If shared/mutable, make a detached snapshot or use immutable persistent subtrees; merely casting a pointer is invalid.
3. All required async-initialized semantic values are ready and validated before producing a hashable frozen artifact. External lazy resolution may remain as separate key-based state, not hash-relevant mutable payload.
4. Frozen file/arena layout and storage-policy IDs are fixed; changing representation produces another artifact/revision.

Public API sketch (proposed syntax, not verified grammar):
```simple
var node = AstNode(value = 10)
let live: Immutable<AstNode> = node.immutable()
let rev: RevisionImmutable<AstNode> = node.snapshot()
let frozen: FrozenImmutable<AstNode> = node.frozen_copy()
node.value = 20       # allowed via mutable authority, with required synchronization
# live.value is 20; rev.value and frozen.value remain 10
live.value = 30       # compile error: read-only view
```

## 3. Async initialization and strict public-attribute checks

### 3.1 Class capability, per-field producer, and completion
`@support_async_immutable` authorizes deferred construction; it must not implicitly mark omitted fields valid. At every constructor/copy/factory/publication boundary, each required field must be either definitively initialized by a synchronous expression, or bound to a typed, valid async producer registered **before the partially initialized node escapes**.
```simple
@support_async_immutable
class HirNode
    id: NodeId
    body: HirExpr
    inferred_type: TypeId
let a = HirNode(id = id, body = expr, inferred_type = known_type)
let b = HirNode(id = id2, body = expr2, inferred_type = async infer_type(expr2))
let c = HirNode(id = id3, body = expr3)  # E_ASYNC_INIT_MISSING
let read_only: Immutable<HirNode> = b.immutable()
let resolved = await read_only.inferred_type  # explicit suspension
```
Illustrative. Prefer reusing Simple's existing `async` expression and class-attribute grammar. Where the language cannot yet distinguish a deferred field expression, provide a library-level `AsyncInit<T>`/`InitProducer<T>` binding rather than a keyword.
The logical field remains `T`; an internal once-only initialization gate need not remain a permanent `AsyncOnce<T>` wrapper. The gate guarantees *first initialization*, not lifetime constness. An `Immutable<T>` reader observes later synchronized updates; a revision-pinned reader does not.

### 3.2 Definitive public checks
| Condition at constructor/escape/publication | Diagnostic |
|---|---|
| Exported/public field absent and no async binding | **Compile error** `E_ATTR_REQUIRED_UNINIT` |
| `@support_async_immutable` field absent but producer not registered | **Compile error** `E_ASYNC_INIT_MISSING` |
| Async field binding on class without capability | Compile error `E_ASYNC_INIT_UNSUPPORTED` |
| Pending field read without proven readiness/await | Compile error `E_ATTR_NOT_READY` |
| Double registration or completion | Compile-time error when statically evident; otherwise typed runtime failure |
| Producer type differs from declared attribute type | Compile error `E_ASYNC_INIT_TYPE` |
| Producer or mutable alias illegally escapes its region | Compile error `E_INIT_CAPABILITY_ESCAPE` |
| Concurrent unsynchronized mutation read through live immutable view | Reject if statically provable; sanitizer/diagnostics otherwise |
| Freeze/serialize while required semantic fields remain pending | Error/await barrier; never write partial artifact |
Run checks on **effective visibility** (folder privacy, feature-public, `__init__.spl` layer-public exports). Constructor defaults, named constructors, generated getters/setters, cloning, inheritance, generic specialization, ABI/FFI access, field forwarding must participate. Required initialization is path-sensitive.
`NotInit<T>` is not an implicit public optional value. A `None`/`nil` sentinel must not silently discharge a required non-optional field.

### 3.3 Runtime protocol
Lifecycle: `Unregistered` -> `ProducerClaimed` -> `Ready | Failed | Cancelled`. Registration before exposing a pending node. Single-use completion permit; release-store on readiness, acquire-load on read. Failed/cancelled wakes every waiter. Retry uses a fresh attempt/generation, never resets a published cell. Track producer/consumer edges to detect cyclic waits. Build-attempt/epoch fences so stale tasks can't populate a new snapshot. Fiber waiting uses the existing scheduler/single-flight infra, no busy-wait. Group-ready barrier optional.

### 3.4 Fast layout
No async machinery for classes/nodes without pending fields. Initialization state for active pending slots only, in a pooled side table keyed by `(arena, generation, node, attr)`; compact bitmap/group wait record. Initialized field access identical to direct load/store when readiness is proven. Separate immutable semantic payload from mutable resolution caches. Runtime async handles, wait queues, owner pointers, locks are **not serialized** in the AST/HIR/MIR cache.

## 4. One unified node-attribute schema and three storage backends
Canonical typed attribute description in compiler common/HIR metadata; reuse existing node-attribute and generated get/set facilities. Metadata: `AttrId` + qualified name; declared `TypeId` (one name -> one type per node tree); visibility/owner; required/default/init mode (sync required, default, async-registered, internal NotInit); mutability/access capability; virtual/computed getter/setter; logical field/column identity; storage hint (`auto|embedded|indexed|hash`, policy not semantics); revision/cache participation.
4.1 Embedded (AoS): dense hot fields; fixed offsets; no hash/virtual/policy branch.
4.2 Indexed SoA columns: NodeId -> arena-local dense index; lazy per-column; presence bitmap (absence != zero); RegionId/generation checks.
4.3 Sparse hashmap: one pooled arena map keyed by `(local node index, AttrId)`, not a heap map per node; integer IDs at runtime; small-vector specialization allowed.
4.4 Auto choice by profile (dense+hot -> embedded; dense scanned -> SoA; rare point lookups -> shared sparse hash; very small sparse -> arena small-vector if benchmarked; unknown -> conservative static + collect profile). Thresholds are config/profile parameters. Reuse existing collection switching and SoA/AoS abstractions.

## 5. Profile-guided containers and static/runtime switching
5.1 One `ContainerPolicy {storage, selection: static|runtime, profile: off|sample|full, layout: aos|soa|auto, switch_hysteresis, memory_budget, latency_budget}` reused by arrays, maps, dataframes, resource stores, node-attr tables; implemented with existing SDN config + annotations (e.g. `@storage(auto)`); priority: explicit source/ABI > explicit build policy > validated profile policy > deterministic heuristic.
5.2 Static selection (compiler default): choose backend at build/HIR/snapshot time from schema + profile; specialize accessors; persist `StoragePolicyId` + provenance + physical-layout ABI version; semantic HIR/MIR key independent of physical choice; ABI-layout/OBJ keys include it. PGO from XRay/collection profiles; release ships chosen policy without profiling.
5.3 Runtime selection (opt-in, mutable containers): EWMA/sampled metrics per container/arena; switch when gain > conversion cost + hysteresis over a min observation interval; cooldown; migration budget. Migration transaction: choose under ownership token; build new representation copying logical (AttrId, value, init-state); fence writers / safepoint; atomically publish new representation generation; keep old representation for pinned readers (lease/epoch/RCU); record receipt. Immutable live view sees new layout only after publish; RevisionImmutable stays pinned; FrozenImmutable never switches in place; iterators generation-checked.
5.4 Cost control: per container/arena; single dispatch at the handle boundary; static/frozen paths compile it away; devirtualize generated accessors; prefer changing policy for the next build/revision. Compiler AST/HIR/MIR default: static layout per artifact; runtime adaptation for long-lived LSP/workspace stores, caches, build-runner indexes, general collections.
5.5 Conceptual SDN: `compiler.node_attrs: {default_storage: auto, selection: static, profile: off, profile_input: build/attr_profile.sdn, freeze_layout_on_publish: true}`; `tooling.workspace_attrs: {default_storage: auto, selection: runtime, profile: sample, switch_hysteresis: 0.25, min_observation_ops: 10000, max_migration_memory_ratio: 0.20}` (placeholders; validate against real SDN parser).

## 6. Layer responsibilities
Parser/AST (10.frontend): parse annotations/field syntax/async initializer exprs; spans; compact nodes; no per-node maps, no offsets, no semantic attr identity. HIR: resolve AttrId, TypeId, visibility, default/producers, definite init, read-only capability, generated getter/setter, storage hints; no ABI layout. Canonical MIR (50.mir): typed field projections/loads/stores/await/readiness effects; ownership/revision boundaries; no per-backend MIR variants. Target/layout lowering: specialize to offset/column/pooled hash; inline getters; compile away static policy. Interpreter (95.interp): same schema/init/checks via shared helpers. LSP/tools: live views for active parse, revision snapshots for retained docs, quick fixes. Driver/cache (80.driver): semantic vs physical keys, receipts, codecs, invalidation; never serialize wait queues/locks/pointers/incomplete payloads. Collections/runtime: ContainerPolicy, adaptation, leases, profile — not a second node-only switching engine.
HIR decision: handle attribute semantics in HIR via a logical descriptor `ResolvedAttr {owner_type, attr_id, value_type, visibility, initialization: Required|Default|AsyncRegistered|InternalNotInit, access: Mutable|ReadOnly|RevisionPinned|Frozen, storage_hint, source_span}` — extend existing HIR field-projection metadata. Tree schema canonical at HIR/type-check: same name -> one type.
MIR: reuse existing field/index/map ops; logical AttrProject only if deferred physical choice requires; lowered before backend; readiness checks only where pending, eliminated after proven await; effects through existing effect/ownership system.

## 7. Versioning, cache, identity
Separate logical NodeId + schema/owner identity, revision/generation, physical StoragePolicyId. Semantic change -> new revision and dependent invalidation. Representation-only migration changes physical/OBJ key, not neutral HIR key. Async values contributing to an artifact hash resolved before hashing. LSP edit = new document revision; old RevisionImmutable handles valid until lease release; generation-check reused node IDs. Frozen payloads pointer-free, versioned codecs; rebuild runtime tables after load. Honor XXH3 vs stronger trust-boundary hash policy.

## 8. Performance targets (proposed admission budgets, not measured)
No new annotations: cold compile overhead <= 2% median, peak RSS <= 3%. Embedded access after specialization: no added hash/virtual/atomic. Static SoA scan comparable to best existing SoA. Sparse attrs: less memory than dense rare fields. Async absent: zero per-node async allocation, no ready branch on proven paths. Runtime switch disabled: no counters/migration on hot path. Runtime switch enabled: benefit > conversion+sampling+retention cost. Revision snapshot stable under concurrent edits. Frozen cache byte-stable and warm-load parity.
Benchmark matrix: 10K/100K/1M nodes fused/separated pipelines; density 100/50/10/1/~0%, 1/4/16/64 attrs; sequential/random read/update/batch/virtual/profile on/off; embedded/SoA/bitmap+column/small-vector/pooled hash cold/warm; async 0/1/10/100% pending, failures, contention, 3000 keys; snapshots 1/10/100, edit 1 vs 1000 nodes; runtime adaptation stable/sudden/alternating(thrash)/OOM abort/long readers; 32/64-bit x86/ARM/RISC-V robust/debug/CI/release. Metrics per phase: wall/CPU, allocations, peak RSS, bytes/node, cache/branch misses, serialized bytes, update throughput, P50/P95/P99, migrations, reuse ratio, diagnostic completeness. Integrate with existing XRay/perf infra.

## 9. Implementation sequence and gates
P0 Source inventory / non-duplication gate: inspect node declarations, HIR field resolution, MIR get/set/index/map, generated accessors/aspects, collections, profile/XRay, NotInit, async fibers, visibility, cache codecs, diagnostics, build-runner schema; produce symbol-to-requirement map (owners, tests, current behavior, gaps). Do not replace existing modules that satisfy a contract. Confirm parser/SDN syntax before promising examples.
P1 Shared attribute semantics + public initialization: AttributeSchema/AttrId, type/visibility checks, single definite-initialization verifier; compile errors for exported non-async missing attributes (incl. generated/public getters) and unregistered async omissions under @support_async_immutable; shared diagnostic engine + auto-fix; SSpec acceptance scenarios first; legacy audit with a separately gated migration mode only if unavoidable — normal new-code semantics remain errors.
P2 Read-only capabilities and revisions: Immutable<T> projection over ownership, then RevisionImmutable<T> (leases/structural sharing), then FrozenImmutable<T> (move-or-copy proof); reuse immutable cache snapshots and LSP overlays. Tests: aliasing, nested fields, mutating methods, FFI/unsafe, generics, array/map children, deletion/reuse, old-reader lifetime, trait/generic conversions.
P3 Async registered initialization: class annotation, producer binding, flow-sensitive readiness, once-only permits, scheduler waiters, cancel/error, cycle detection, attempt fencing; sidecars for pending fields; compiler elimination on proven-ready paths; no nil/Option uninit loophole; no hash while pending.
P4 Storage backend unification: typed attrs mapped to embedded/SoA/indexed/hash via one generated get/set; preserve virtual accessors/aspects, inheritance, tree-wide same-name/same-type; HIR ResolvedAttr -> MIR specialization, interpreter access, stable codec schema; prove no added indirection on embedded path.
P5 Static profile-guided selection: policy SDN, profile schema, physical-layout cache key; select once per build/snapshot; train on XRay/collection traces; statistical perf regression; reproducible default; provenance.
P6 Opt-in runtime container switching: sampled counters, hysteresis/cooldown, migration budget in the shared container implementation; per container/arena; atomic publish; retain old-reader layouts; fence writers; invalidate stale iterators; receipts; start with long-lived tooling/runtime stores; never migrate frozen compiler artifacts in place.
P7 Integration, proofs, release: tests across compiler/interpreter/LSP/build/cache/backends; Lean model where supported; diagnostics/auto-fix text, serialization determinism, replay, source maps, rollback; feature/config gates first, default after evidence meets budgets.

## 10. Mandatory acceptance tests (SSpec inventory; expected-fail until their phase lands)
IMM-01 mutation through Immutable<T> -> compile error + location + fix. IMM-02 other synchronized mutable alias writes -> live view sees new value. IMM-03 revision pinned before mutation -> old value stable, new revision new value. IMM-04 mutate frozen / escape mutable alias -> compile error or safe copy. ASY-01 all sync-initialized -> pass, no async allocation. ASY-02 valid async producer -> pass, explicit await, correct value. ASY-03 public field omitted without async binding -> compile error even on annotated class. ASY-04 missing under @support_async_immutable but unregistered -> compile error. ASY-05 async-bound field without class authorization -> compile error. ASY-06 producer mismatch/duplicate/failure/cancel -> correct error; all waiters wake. ASY-07 dependency cycle + stale build attempt -> diagnosed, no hang/stale publication. ASY-08 async unused in dense AST -> no extra slot/lock per node. ATTR-01 same name conflicting tree types -> compile error with both definitions. ATTR-02 generated getter/setter/virtual/aspect across each backend -> same semantics/visibility. ATTR-03 array/index/hash with sparse/default/NotInit -> exact parity, no absent==zero. ATTR-04 feature/layer public vs folder-private -> correct export + init check. ATTR-05 HIR->MIR specialization + diagnostics -> no drift, direct access. REV-01 concurrent LSP edits with old pinned readers -> stable, safe reclamation. REV-02 frozen serialization/reload -> identical, no pointers persisted. PROF-01 static policy change from profile -> same behavior, physical cache invalidation. PROF-02 runtime migration with active readers -> atomic, no UAF/torn reads/stale iterators. PROF-03 oscillating workload -> hysteresis prevents thrash. PERF-01 feature disabled -> baseline budgets met. PERF-02 embedded hot accessor -> no new virtual/hash/atomic. Extended: malformed source, parser recovery, generic attrs, inheritance, nested arrays/maps, FFI, debug/release, 32-bit.

## 11. Diagnostics and LSP auto-fixes
Shared diagnostic builder, spans, multiple suggestions, compiler/interpreter/LSP mappings: E_ATTR_REQUIRED_UNINIT, E_ASYNC_INIT_MISSING, E_ATTR_NOT_READY, E_IMMUTABLE_WRITE, E_FROZEN_ALIAS, E_STORAGE_POLICY_CONFLICT (messages + fixes as in the original). Never auto-insert nil/None/raw Option public field/unchecked cast to silence required-initialization errors. Protect source maps across generated accessors and storage lowering.

## 12. Risks (summary)
Immutable assumed snapshot-stable (document; pinned revision in snapshot APIs); annotation concealing missing fields (strict registration checks); producer never completes (terminal failed/cancelled, cycle detection, fencing); per-node async bloat (sidecars only for pending); HIR exposing layout (logical descriptor); duplicate profile logic (one ContainerPolicy/XRay pipeline); profile instability (static default, hysteresis, receipts); migration breaking iterators (generation, scoped borrows, atomic publish, leases); frozen cache changes on layout switch (new physical artifact, semantic key unchanged); hot-field slowdown (compile-time AttrId, offset specialization); 32-bit overhead (bounded metadata, no mandatory GC/RC); interpreter/parser divergence (central schema + parity SSpec).

## 13. Definition of done
One source-of-truth attribute schema + generated accessors used by compiler, interpreter, parser tools, LSP. Distinct documented live/pinned/frozen semantics. Missing non-async public attributes are compile errors; async annotation never excuses an unregistered field. Embedded/SoA/sparse hash interchangeable via typed accessors. HIR owns attribute type/visibility/init semantics; physical strategy specialized later; no duplicated MIR family. Static PGO selects compiler storage policy; runtime switching opt-in, container-granular, concurrency-safe, never mutates pinned/frozen snapshots. Cache identity, schema versioning, pointer-free persistence, rollback/repair, source traceability survive. Regression/stress/perf evidence meets budgets.

## 14. References
github.com/ormastes/simple; Kotlin collections overview; OpenJDK Collection docs; Roslyn Red-Green Trees; Tree-sitter advanced parsing; rust-analyzer syntax doc; Rust OnceLock; Marlow et al. Monad-Par (IVars); Kuper et al. LVars; Salsa; MLIR LangRef; LLVM Programmer's Manual; Redis memory optimization; Linux RCU whatisRCU; Futhark uniqueness types.

Implementation caution: this is a proposed architecture and phased acceptance plan, not a claim of source changes, compiler support, passing tests, or benchmark numbers. P0 must map it onto the actual repository and preserve/extend existing infrastructure.
