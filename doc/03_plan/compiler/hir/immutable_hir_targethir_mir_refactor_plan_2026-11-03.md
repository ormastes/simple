# Simple: Immutable HIR / TargetHIR / MIR Refactoring Plan

**Date:** 2026-11-03 (KST)

**Status:** Design and implementation plan; no compiler source modified, no native test executed

**Repository:** [`ormastes/simple`](https://github.com/ormastes/simple)

**Suggested repository destination:** `doc/03_plan/compiler/hir/immutable_hir_targethir_mir_refactor_plan_2026-11-03.md`

**Basis:** Existing Simple cache, SCV, generic/AOP/macro, Phase 3, schema-transition, and current HIR/MIR source contracts. GitHub connector code-search results referenced `97700b29e10675867891503f1e634b50a192356d` on the default branch; individual source files were fetched from `main` during this review. This is a *scoped source-and-plan audit*, not an entire repository build or live CI certification.

## 0. Decision

**Keep one deeply immutable, reusable semantic HIR snapshot. Construct a small, strongly typed `TargetHIR` wrapper around that snapshot and a separately immutable, target-bound resolution overlay. Lower each target into its own MIR with private worker scratch.**

```text
Source snapshot + semantic read witnesses
  -> HIRBuilder (private mutable construction)
  -> freeze/validate -> HirSnapshot (deeply immutable, reusable)
       |
       +--> TargetHIRBuilder(target A, only needed regions)
       |      -> freeze -> TargetHIR(A) -> MIRLowerer(A) -> MIR(A) -> OBJ(A)
       +--> TargetHIRBuilder(target B, only needed regions)
              -> freeze -> TargetHIR(B) -> MIRLowerer(B) -> MIR(B) -> OBJ(B)
```

Important distinctions:

1. **No per-HIR-node subclass or concrete wrapper allocation.** One `TargetHIR` is a typed view of a snapshot or independently ready function/region; it does not duplicate the HIR tree.
2. **No raw overlay access from MIR code.** Target-sensitive reads go through typed `TargetHIR` methods. The overlay is private, with dense indexed storage for hot values and sparse storage for cold exceptions.
3. **HIR is genuinely immutable, not merely a mutable graph passed through a `val`.** Freezing verifies exclusive construction ownership, prevents subsequent mutation through aliased Dict/list/class references, assigns snapshot ownership and version, and publishes through an acquire/release-safe handle.
4. **The published target overlay is also immutable.** The builder may mutate its private tables; `TargetHIR` cannot. Later discoveries produce new immutable region artifacts or a new snapshot, not post-freeze writes.
5. **`MirLowering` and `MirBuilder` remain mutable, private, per-lowering-session scratch.** An immutable *input* does not require freezing the algorithm's scratch state before MIR has been emitted.
6. **No whole-program preparation barrier.** Per-module/function/region readiness supports the existing fused source-to-OBJ path; do not force full HIR/TargetHIR serialization or freezing of all modules before the first MIR function starts.
7. **Semantic target dependence is not silently deferred.** Target-dependent parsing, imports, name resolution, type checking, constant evaluation, `@when` and ABI-dependent public signatures require an appropriately constrained HIR variant or an explicitly verified symbolic obligation.

**Naming:** Keep existing `HirModule`, `HirFunction`, and `HirExpr` definitions for compatibility. Introduce `HirSnapshot` (frozen owner), `HirTargetConstraints` (portable semantic obligations), `TargetHIRBuilder` and `TargetHIR` (strong target-bound interface), and `TargetHIRResolution` (private overlay). Do **not** rename the common representation `AbstractHIR` or `HIRAbstract`; those names neither assert immutability nor identify target independence.

## 1. Existing plans reconciled

| Existing baseline | Preserved contract | Explicit refinement here |
|---|---|---|
| `simple_cache_async_build_final_design_2026-10-26.md`, especially §§4, 7–9, 17, 20 | Pseudo-immutable artifact sets, optional OS/CPU semantic constraints, canonical storage, source→OBJ default, partial variants, collision-safe compact IDs, fiber/process execution | Split semantic *constraints/obligations* retained in HIR from concrete target *resolution* in a frozen overlay; use a typed wrapper at the module/region boundary, not per node |
| `simple_cache_with_scv_implementation_plan_2026-10-27_sosix_rr_updated.md`, §§12, 19, 31–32 | Immutable AST/HIR/MIR/OBJ sets, SCV witnesses, no global serialization barrier, target-aware invalidation, S1→S2→S3 release sequencing, `.rr` fail-closed reconciliation | Add an independently addressable, immutable TargetHIR-resolution layer and `TargetHIR` API without declaring S3 complete |
| `simple_tldr_generic_aspect_macro_cache_plan_2026-10-24.md` | Symbolic generic template TLDR, immutable concrete typed TLDR views, aspect selector/advice dependencies, macro uses and reverse references | HIR preserves generic semantic identity; TargetHIR binds only demanded ABI/layout/ISA effects, MIR specialization and object identity remain separate |
| `doc/03_plan/compiler/phase3_incremental_build_completion_2026-10-13.md` | Usable Stage 3/4, keep good artifacts, source-to-object and real native validation, no false success status | Structural refactor remains feature-gated until current Stage 3/4 and representative multi-module baselines pass; avoid costly rewrite of actively changing MIR |
| `spec/compiler_schema/transitions/hir_expr_to_mir.sdn` and sibling statement/type mappings | The declared HIR variant universe, explicit unsupported diagnostics and tests are authoritative | Add `TargetHIRResolution` coverage as an additional boundary; never mask Missing/Unsupported variants or remove existing transition rows |
| Prior node-attribute / SoA/AoS / RegionId plans (2026-11-01) | Node kinds are typed, `NotInit<Node>` is an initialization state, `RegionId` and `ObjId` are distinct, attribute container switching is profile/config driven | Resolution ownership is by typed ID and region; `NotInit` is builder-only and must never appear in an admitted immutable snapshot; no user-visible tag added to nodes |

### Contradiction resolved: optional target information in HIR

The October 26 plan explicitly permits optional OS/CPU/ABI/layout/runtime information in HIR. **Do not delete those semantic constraints.** Model them as *observed target-read witnesses, selected semantic branch identity, constraints, and deferred obligations*. The `HirSnapshot` is reusable only if a new target satisfies those constraints. Concrete pointer offsets, actual ABI registers, native SIMD choice, runtime linkage and target backend features belong in `TargetHIRResolution` or later MIR/codegen.

`os=None` / `cpu=None` means **the corresponding semantic dimension is proven unconstrained or represented by a validated deferred obligation**. It must not mean “unknown”, “use local host”, or “not initialized.” An unverified legacy HIR has no portable authority and must be rejected/revalidated.

### Contradiction resolved: strictly immutable snapshots versus pseudo-immutable cache slots

Previous cache plans permit write-once scalar/array/map memo slots. Those may remain **external synchronization/cache metadata** (a slot transitions Pending→Ready with an immutable value). They may not mutate a published `HirSnapshot` or `TargetHIRResolution` payload. Logical immutability, write-once publication, and private mutable builders are separate notions.

## 2. Scoped current-source findings and migration constraints

This table describes inspected source, **not proof that the entire current compiler works**:

| Current source / spec | Observed constraint | Required migration action |
|---|---|---|
| [`src/compiler/20.hir/hir_types.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_types.spl) | `HirModule` has many `Dict`, list, `SymbolTable` fields, followed by defaulted metadata; no dedicated `target_context` field in the inspected declaration. Comment warns about positional seed construction. | Keep existing field order; append defaulted compatibility metadata only if essential. Prefer `HirSnapshot` owner outside the existing `HirModule` until seed/bootstrap qualification. Deep-freeze nested containers. |
| [`src/compiler/20.hir/hir_definitions.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_definitions.spl) | HIR functions/classes/fields carry generic, GPU, visibility, platform, effect and layout-related metadata. | Classify each field as semantic core, semantic target constraint, or target-lowering result; do not relocate source-observable declarations into the MIR layer. Preserve positional/desugared Option forms. |
| [`src/compiler/20.hir/hir_codec.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_codec.spl) | Module-local SymbolIds, current generated codec and decode/encode equivalence contract; canonical encoder entry currently explicitly refuses with `canonical_codec_generator_stale` until generation is admitted. | Do not assume canonical codec is ready. Version new frozen artifact sections; verify semantic cold/warm equivalence and full consumer behavior, not only round trips. |
| [`src/compiler/00.common/mir_target_context.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/00.common/mir_target_context.spl) | `MirTargetContext` already owns arch, OS, ABI, backend, version and collection settings, with legacy host/native fallback normalization. | Reuse it through an explicit resolved target descriptor/adapter; do not add an inconsistent second normalization authority. For portable-cache proofs, forbid ambient host fallback unless the *compile request* explicitly resolved `native` into a recorded target identity. |
| [`src/compiler/50.mir/mir_lowering_types.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/mir_lowering_types.spl) | Large mutable `MirLowering` state with many maps, arrays, transients and diagnostics. | Keep mutable session scratch private; do not copy it into TargetHIR. Introduce one lowerer construction factory and pass the target view/context once. |
| [`src/compiler/50.mir/_MirLowering/module_lowering.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/module_lowering.spl) | Module/metadata lowering already uses target context and external reverse-reference/owner facts. | Replace individual target-sensitive HIR reads behind typed methods in small slices, keeping all current authority and dependency writes. |
| [`src/compiler/50.mir/_MirLowering/asm_and_targets.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/asm_and_targets.spl) | Inline-assembly alternatives are matched against target arch/OS/ABI/backend during MIR lowering. | Resolve selected arm with a frozen target overlay or a target-bound function view; preserve ordered matching, nonexhaustive diagnostics and explicit compile-error arms. |
| [`doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md`](https://github.com/ormastes/simple/blob/main/doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md) | Existing checks enforce one `MirTargetContext` across driver, bootstrap, nested lowerers and backend/JIT/C paths. | Extend—not delete—these source contracts. `TargetHIR` must preserve context equality, or use an adapter with exactly the same normalized value. |
| [`src/compiler/50.mir/_MirLowering/archive_borrowed_module_v1.spl`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/archive_borrowed_module_v1.spl) | Borrowed HIR→MIR path verifies source module, full body digest, declaration owner/authority, and active transient scope. | `TargetHIR` cannot be a shortcut around final HIR admission. Pin parent snapshot through lowering, and preserve exact declaration/body/lease checks. |
| [`spec/compiler_schema/transitions/hir_expr_to_mir.sdn`](https://github.com/ormastes/simple/blob/main/spec/compiler_schema/transitions/hir_expr_to_mir.sdn) | Explicit variant-by-variant implemented/unsupported mapping and diagnostics. | Add overlay-resolve coverage for target-sensitive variants; never weaken exhaustiveness when changing the MIR input type. |

Historical HIR/MIR un-stub plans and Stage 3 bug records are **not current pass results**. Current upstream may include partial fixes that need regression tests rather than reimplementation.

## 3. Package ownership and public API

### 3.1 Incremental package placement

Keep the established Simple source layout, not a parallel compiler:

```text
src/compiler/
  20.hir/
    hir_types.spl                   # existing; stable public HIR definitions
    hir_definitions.spl             # existing
    hir_snapshot.spl                # NEW frozen semantic root/typed local ids
    hir_target_constraints.spl      # NEW target reads and obligations
    hir_freeze.spl                  # NEW builder sealing/ownership validation
    hir_codec.spl                   # existing; versioned migration
    target_hir/                     # NEW second package, bounded files
      target_hir.spl                # opaque concrete typed view
      target_hir_builder.spl        # private mutable resolution producer
      target_hir_resolution.spl     # frozen dense/sparse overlay
      target_hir_validate.spl       # compatibility/identity guards
      target_hir_codec.spl          # optional separate cache section
  00.common/
    mir_target_context.spl          # existing normalization authority
  50.mir/
    mir_lowering_types.spl          # existing private mutable scratch
    _MirLowering/...                # migrate consumers incrementally
```

If the repository's one-file/source-length limits differ by module, use existing split-module/export patterns; no new monolithic 800+ line source is required. Keep `HirModule` and the existing MIR module names import-compatible during transition. Package boundary should restrict MIR from importing internal `TargetHIRResolution` or calling mutators.

### 3.2 Proposed types (API intent, not verified Simple grammar)

```simple
struct HirSnapshot:
    id: HirSnapshotId
    module: FrozenRef<HirModule>            # deep-frozen, not a mutable alias
    constraints: HirTargetConstraints
    semantic_witnesses: SemanticReadSet
    schema: HirSchemaId

struct TargetHIR:
    hir: &HirSnapshot                    # PRIVATE to target_hir package
    target: ResolvedTargetId             # normalized, complete target
    region: RegionId
    resolution: FrozenRef<TargetHIRResolution>  # PRIVATE
    identity: TargetHIRIdentity

struct TargetHIRResolution:
    hot_layout_by_type: DenseIndex<ResolvedLayout>
    hot_abi_by_function: DenseIndex<ResolvedABI>
    sparse_exceptions: SparseIndex<ResolutionValue>
    selected_guard_arms: DenseOrSparseIndex<SelectedArmId>
    resolved_obligation_evidence: ObligationProofSet

TargetHIRBuilder.new(hir, target, region)
TargetHIRBuilder.resolve_required()
TargetHIRBuilder.freeze() -> Result<TargetHIR, ResolutionError>

TargetHIR.node(id: HirNodeId) -> HirNodeReadOnly
TargetHIR.layout(id: HirTypeId) -> Result<ResolvedLayout, ResolutionError>
TargetHIR.abi(id: HirFunctionId) -> Result<ResolvedABI, ResolutionError>
TargetHIR.guard_arm(id: HirNodeId) -> Result<SelectedArm, ResolutionError>
TargetHIR.simd(id: HirNodeId) -> Result<ResolvedVectorOperation, ResolutionError>

MirLowering.new_for_target_hir(target_hir: &TargetHIR, private_scratch: MirScratch)
    -> MirLowering
```

The read API may expose specialized view objects as **small borrowed values or inlined handles**, not heap-allocated per-node wrappers. `HirNodeId`, `HirTypeId`, `HirFunctionId`, `RegionId`, and `ObjId` are distinct types; 32-bit local indices may be used where capacity permits. Node IDs are **scope-qualified by snapshot/arena identity** and never treated as globally unique hashes.

**Important safety property:** `MIRLowerer` must accept `TargetHIR` only, not `HirModule` or raw `HirSnapshot`. A target-dependent operation cannot get a default ABI/layout by bypassing the view. Existing `MirLowering.new_for_target(SymbolTable, MirTargetContext)` remains a compatibility adapter while callers migrate; do not delete it until all source-specs, bootstrap and plugins are retargeted.

### 3.3 Compile-time versus runtime enforcement

| Hazard | Compile-time rule | Runtime/cache validation |
|---|---|---|
| Raw HIR passed to target-dependent lowerer | Distinct nominal `HirSnapshot` and `TargetHIR` types; private constructors | Reject legacy adapter calls once migrated |
| Cross-snapshot/region ID mix | Distinct typed IDs and borrowed view lifetimes | Check snapshot/arena/generation for external or persistent IDs |
| Windows overlay used on Linux MIR | `TargetHIR` carries its own bound context; no free target parameter in consumer | Exact normalized `ResolvedTargetId` and observed-feature matching |
| Unresolved value read | `ResolvedLayout`/`ResolvedABI` are different from symbolic HIR types | `Result` with named diagnostic; no silent fallback or implicit nil→zero |
| Mutation after freeze | Private builder, read-only fields, no writable aliases | Freeze audits ownership; optional debug checksum/assertion |
| Stale/incompatible cache hit | Stage-typed cache refs | Producer/schema/context/source/semantic read/SCV witness validation |

Nominal typing alone does not prove two *runtime* target values are equal; the target fingerprint checks remain mandatory.

## 4. Correct target/host/semantic separation

| Variation | Portable HIR | TargetHIR | MIR or codegen |
|---|---|---|---|
| Fixed-width integer operation | Semantics and overflow requirements | Usually no entry | Select native instruction |
| `usize`, pointer width, `sizeof`, `alignof` | Symbolic operation plus any compile-time observed layout witness | Resolved width/layout | Concrete typed operation |
| Endian operations | Logical endian contract and explicit read witness | Native/virtual target byte ordering | Conversions, loads/stores |
| Type/field layout and bitfields | Fields, packing attributes, semantics | Offsets, alignment, ABI class | Loads/stores and ABI lowering |
| SIMD `@simd` | Required vectors, lane operations and semantic restrictions | Legal lanes/ISA feature choice when needed | AVX/AVX-512/NEON/SVE/RVV or fallback |
| OS/sosix API | Logical API/effect and availability constraints | Target OS/runtime dispatch decision | Concrete backend call/link |
| `@when` and static conditional import | **Only when semantic branches remain valid**; actual target-specific parse/import/name/type facts must be separately keyed | Deferred target selections where semantic proof permits | Selected code path |
| Inline asm match | All valid arms plus target-exhaustiveness obligations | Exact selected arm or error | Native asm lowering |
| Generic template / concrete TLDR | Template and typed instance/semantic dependency identity | Target-bound instance layout and ABI where needed | Demanded specialization and object |
| Static aspect/macro effects | Exact woven semantic effects and selector/use witnesses | Target-specific effect/selection when appropriate | Target-specific advice dispatch and emitted code |
| GPU/VHDL/backend-specific semantics | Capabilities and symbolic intrinsic requirements | Valid capability/legalization choice | Device/backend-specific IR |
| Compiler machine's current OS/CPU | **Not a default target** | Only explicit normalized `native` request, recorded in key | Worker execution concerns separate |

**Early semantic split:** `@when` in the Rust seed parser is already evaluated against a target. An OS/CPU condition can change tokens, imports, declarations or diagnostics before HIR exists. Its resulting HIR cannot be declared universally portable simply by moving the target field out. Share only identical verified semantic subgraphs or build separate constrained HIR roots. The cache records *positive and negative* target queries and dependent imports. Do not evaluate target-specific `@when` blindly in MIR if it changes semantic input.

**Target normalization:** `MirTargetContext` is the existing authority but its legacy helper can derive OS from host for unknown target text. A *strict* target-cache admission path must reject unknown or ambiguous tuples rather than treating host fallback as proof of portability. `native` is resolved once at the action boundary; the normalized target, not the ambient host, enters artifact identity.

## 5. Immutable lifecycle, concurrency and memory safety

### 5.1 Lifecycle and publication

1. Start a private `HIRBuilder`/semantic owner from an admitted source/SCV snapshot. `NotInit<T>` is legal inside the builder only; uninitialized required fields block freezing.
2. Validate complete semantic reads and dependency witnesses, deterministic symbol ordering, all required operands and type constraints. Detect illegal recursion/cycles and unresolved symbols rather than freezing partially initialized objects.
3. Deep-freeze the HIR graph: no mutable `Dict`, list or reference alias escapes; adopt frozen arena/compact arrays and an immutable root handle. **Do not copy entire HIR per target.** Preserve module-local `SymbolId` semantics and stable codec order.
4. Publish only a complete `HirSnapshot` to the cache/sidecar index with a release-store and durable/admitted receipt as required. Readers acquire the ready handle and a lifetime pin. Failed/cancelled builders publish no success.
5. `TargetHIRBuilder` obtains the exact pinned parent snapshot and target; resolves **only demanded regions** to a private dense/sparse table, with independent target-read proof and no reference to mutable compiler scratch.
6. Freeze an immutable `TargetHIR(region)` with parent snapshot/version, normalized target ID, required resolved obligations, and its own digest. Publish as a distinct stage artifact.
7. MIR worker receives a read-only `&TargetHIR`, allocates private `MirLowering` scratch and emits its own MIR function/module. On failure, discard scratch and unpublished output, preserving parent snapshots.
8. Release pins after consumers finish; eviction/pack compaction retains old memory while readers are active. Canceling one waiter must not cancel a shared producer still demanded by others.

No central mutex/file lock/lease is introduced on the strict compile hot path. A first-requester maker + awaiters may own a mutable **slot state machine external to the immutable payload**; final publication must have correct acquire/release and ABA protections. Preexisting SCV/journal durability fences remain intact.

### 5.2 Per-region readiness, not a whole-module barrier

The existing default is fused `source→OBJ`. Preserve it with region/function views:

```text
Frozen semantic module skeleton / relevant function body
   -> TargetHIR(region R) Ready
   -> MIR(R) -> OBJ contribution(R)

Other regions can still be constructing/resolving concurrently.
```

The ready region must have a proven dependency closure (including public type layout, needed generic specialization and AOP obligations). A missing proof widens the region or defers readiness; never manufacture “ready” from an incomplete function record. Legal declaration SCCs have group-level admission where necessary. No unconditional serialize→decode cycle occurs between HIR and MIR in the same process.

### 5.3 Deep immutability versus accidental shallow freeze

Existing `HirModule` contains nested mutable collections and `SymbolTable`, so freezing only the outer struct is insufficient. Implement one of:

- Frozen arena representation with immutable container handles and explicit ownership transfer (preferred).
- Persistent immutable arrays/maps with structural sharing and no mutable aliases (acceptable for partial updates).
- Copy into an immutable compact representation when ownership cannot safely be transferred (migration fallback, cost separately measured).

Do not presume `val` or a readonly method signature prevents a hidden alias from writing a nested collection. Introduce debug-only mutation tripwires and, where feasible, a sealed ownership type with no mutable interface.

## 6. Overlay storage and performance policy

### 6.1 Hot/cold storage

| Data | Default representation | Reason |
|---|---|---|
| HIR nodes and common semantic fields | Immutable arena + typed indexed references | Zero per-node wrapper allocation, locality |
| Frequently demanded type layout and function ABI | Packed dense or chunked index over local TypeId/FunctionId | Predictable indexed reads; no per-read hash |
| Rare SIMD override, special asm arm, OS-specific exception | Compact sparse hash/sorted vector (profiled) | Pay only for actual changed nodes |
| Per-region lookup selection | Fixed decision at `TargetHIR.freeze()` | No dynamic algorithm test on every hot access |
| String names / repeated target descriptors | Interned context table and compact IDs | Avoid duplicated target strings |
| Unsupported or unresolved obligations | Structured diagnostic/explicit absence | Never treat absent as a native default |

**Do not decide dense/sparse solely by node count.** If `N` is the number of eligible IDs, `K` the number of resolved entries, `V` the value bytes, `B` the dense valid-bit overhead, and `H` the measured sparse key/table overhead per entry, approximate:

```text
Dense bytes ≈ N × V + B          (or chunked/paged dense allocation)
Sparse bytes ≈ K × (V + H)
Choose based on measured lookup frequency, density K/N, cache locality and RSS,
not a hard-coded universal percentage.
```

Pure dense arrays for all node properties can waste memory. A hash lookup for every type operation can harm single-target compile time. Expose stable typed accessors while specializing the *internal* storage after profiling. Do not perform heap allocations, environment reads or new hashing on every `get_layout()` call.

### 6.2 Evaluation model

```text
M_peak = M_shared_HIR
       + sum(active_target_regions: M_immutable_resolution + M_MIR + M_private_scratch)
       + M_cache_indices + M_reader_pins
```

Sharing HIR does **not** eliminate concurrent MIR working-set cost. Use TaskRunner budget/admission to limit active lowerers by measured peak RSS, not CPU count alone. Retire scratch at function/region completion. Do not retain a full MIR solely to satisfy cache provenance; fused OBJ emission may retain compact provenance references.

### 6.3 Required measurements (report actual counts, not fabricated speedups)

- Baselines: existing compiled path, new typed wrapper with dense hot overlay, sparse-only overlay, and optional per-node-wrapper prototype only as a comparison fixture.
- Targets: 1, 2, 4 and 8 compatible/mixed targets, with separate cold source, cold target-resolution and warm-final-OBJ-hit scenarios.
- Workloads: pure arithmetic, generic-heavy, layout-heavy, `@when`/conditional import, many small functions, SIMD/inline asm, multi-module compiler build and Stage 3 self-hosted components.
- Metrics: wall p50/p95, CPU time, peak RSS and retained bytes, allocation count/bytes, cache hit/miss and fresh constructors, resolutions per field, map probes, contiguous-hit ratio, branch misses/cache misses where supported, serialized bytes, target/region fan-out, pending counts and unexpected re-lowering.
- Proposed gates: **single-target wall p95 regression <=5%** against an equivalent compiler and test environment; zero unbounded memory growth; each cross-target HIR reuse must demonstrate fewer genuine HIR builds with correct output. If the 5% goal is missed, retain the safe wrapper and optimize hot indexed resolution before enabling by default. These are project *targets*, not established measurements.

## 7. Cache and SCV identity design

### 7.1 Artifact graph

```text
Source + TLDR + semantic read proofs
  -> AST semantic variant
  -> HirSnapshot (portable or partially constrained)
     -> TargetHIRResolution(region, target constraint closure)
        -> MIR(region, target, lowering/optimizer version)
           -> OBJ(target, codegen options)
              -> BIN / LIB / SMF
```

Each artifact has an immutable payload and separately admitted publication receipt. OBJ/BIN/LIB/SMF exact hits are checked first; a warm final hit must **not** deserialize HIR merely to validate a downstream result. A target-only change invalidates only stages that actually consumed target information, if semantic-read proofs justify that reuse.

### 7.2 Proposed key ingredients

| Stage | Mandatory key / proof ingredients |
|---|---|
| HIR | Snapshot/source/TLDR/version, semantic compiler/macro/AOP/generic schema, exact positive+negative semantic target reads, dependency/witness manifests, grammar/import/dir metadata, proof of deferred obligations |
| TargetHIR resolution | HIR root and region identity, normalized target descriptor, observed OS/CPU/ABI/layout/runtime/ISA/capability reads, resolution algorithm/schema version, provider identity actually observed |
| MIR | TargetHIR root, region/function body, specialization+weave identity, lowering pass version, optimization policy and relevant instrument modes |
| OBJ | MIR/codegen inputs, target ABI/ISA/object format, backend provider, toolchain/runtime choices and final emitted byte contract |
| Output action | Exact OBJ set, linker/LTO/relocation/config and SCV authority, output durability policy |

Use canonical endian and deterministic byte ordering for persisted sections; *serialization endianness is not target semantics*. XXH3-128 and local 16/32-bit IDs are lookup accelerators, not a substitute for exact identity verification or the existing SHA-256 task/journal trust contracts. Trusted-local and remote/untrusted artifact policy remain distinct.

### 7.3 Migration of prior cache formats

1. Introduce a new target-resolution section/schema with explicit parent HIR identity. Old HIR blobs are read **only through existing validated legacy APIs**, never interpreted as portable because a new optional field is absent.
2. Keep existing valid legacy source→OBJ results when exact current admission still verifies; force miss/regen where new mandatory evidence cannot be reconstructed.
3. Version generated codec definitions, kind registry, and HIR/MIR transition matrices together. A canonical codec path currently marked unavailable cannot become a cache-authority dependency until its generation and native/decoded equivalence gate passes.
4. SCV tracks *source, declaration, directory, macro/AOP and negative-query* changes; compiler owns semantic invalidation. `.rr` publication uses the existing sosix atomic update/recovery contract; on uncertain failure, recheck the entire relevant dependency boundary.
5. `HirSnapshot` immutable content IDs are stable across target workers. `TargetHIR` IDs are separate and include their target-read closure. A reader never combines a target-resolution fragment from a different HIR generation.

## 8. Incremental refactoring work packages

All phases include an independently reversible flag and targeted SSpec. Do not concurrently rewrite the Rust seed, self-hosted Simple HIR, all MIR backends, and cache codec in one patch.

| Phase | Implementation | Safe completion gate |
|---|---|---|
| **P0 — Inventory and baseline** | Record exact source revision, HIR constructors/cloners/codecs, uses of `MirTargetContext`, all MIR lowerer entrypoints, mutation paths, transient scopes, and current Stage 2/3/4 test status. Classify HIR fields as semantic core / semantic target constraint / resolved target value. Capture CPU/RSS baseline. | No source writes; inventory and source/SSpec map reviewed; known active failures separate from newly introduced failures |
| **P1 — Nominal immutable owner** | Add `HirSnapshot`/`HirSnapshotId` and private HIRBuilder freeze; introduce deep-freeze checks without changing MIR access yet. Append required compatibility fields only at legal positions; use owned immutable snapshot references. | Existing codec, HIR semantics, module-local symbol identity, clone/constructor and cold/warm tests green |
| **P2 — Target semantic constraints** | Add `HirTargetConstraints`/observed reads and deferred obligations, including target-dependent `@when` semantic ownership; preserve validated target-specific HIR variants. | Cross-target semantic variants and negative dependency queries never hit wrongly; unsupported target diagnostics explicit |
| **P3 — Typed wrapper + frozen overlay** | Add `TargetHIRBuilder`, immutable `TargetHIRResolution`, opaque `TargetHIR` API, dense/sparse storage and target context canonicalization. No node heap wrappers. | Compile-time API misuse cases fail; multi-target simultaneous immutable reads; freeze validators and no mutable alias |
| **P4 — MIR adapters and readers** | Keep existing `MirLowering.new_for_target` working, but add one new factory that consumes TargetHIR. Migrate layout/ABI, asm guard, SIMD, platform and generic resolution gradually. Retain existing transient owner/digest gates and `MirTargetContext`. | Existing MIR wiring source specs remain valid or explicitly updated; same outputs and diagnostics under old/new paths |
| **P5 — Streaming region resolution** | Region/function TargetHIR ready handles, no mandatory whole-module barrier, local private MirScratch, bounded scheduler admission and scope pins. | Cold streaming, nested functions, SCC, cancellation, same-key 3000 requests, process/fiber modes and release/acquire publication pass |
| **P6 — Immutable cache/codec** | Add TargetHIR section identities and stage-specific invalidation under SCV, test encoded/decoded/mapped direct consumers; promote canonical codec only when generator admitted. | Warm/cold/no-cache semantics, digest/poison cases, source/macro/AOP/negative-query invalidation and crash recovery pass |
| **P7 — Performance optimization** | Profile dense vs sparse hot fields, per-region size, transient allocator, parallel target fan-out, no-change OBJ path. Optimize without changing public safety API. | Performance and RSS gates pass; no measurable cache-correctness regression |
| **P8 — Rollout and legacy removal** | Canary selected Simple modules, then Stage 3 self-hosting and backends, then flag default; retire raw target-dependent HIR/MIR entrypoints only after migration matrix is complete. | Stage 3/4 bootstrap, end-to-end native qualification, CI cross-compiles, rollback tested; source-level code review confirms no unsupported bypasses |


### 8.1 P6 owner decision — per-task private scratch overlay (2026-11-04)

Owner decision: P6 mutable task state uses a **per-task private scratch overlay merged back in owner order**. Each parallel task (module/shard) writes derived TargetHIR/MIR facts into its own overlay over the immutable shared HIR; overlays are never shared or mutated across tasks, and a task reads only base + its own overlay. After completion, overlays merge in stable owner order (ascending `(rank, owner)` = module/shard id, never completion order). The same key from two owners — or an overlay redefining an immutable base key — is a fatal error naming both owners; never last-writer-wins. The merged result is byte-identical for any scheduling or worker count.

Implementation: `src/compiler/20.hir/target_hir/target_hir_task_overlay.spl` (`TaskOverlay`, `overlay_read`, `task_overlay_merge`, `task_overlay_resolve[_for_mode]`), gated by `SIMPLE_TARGET_HIR_MODE` (legacy unchanged; shadow compares merged vs legacy, mismatch fatal; typed uses merged). Spec `test/01_unit/compiler/hir/target_hir_task_overlay_spec.spl` (6/6 on the seed interpreter): determinism across completion orders/worker counts, two-owner conflict fatal naming both, no cross-task visibility, shadow mismatch fatal. The 8 former `BLOCKED-owner` rows of `spec/compiler_schema/target_hir_migration_matrix.sdn` are now `pending` with `pending-stage3`: wiring the MirLowering SymbolTable writers onto `TaskOverlay` needs a frozen HirSnapshot carried into MirLowering (off-limits `module_lowering.spl` constructor/alias site) plus a Stage-3 run.

Wiring (2026-11-04): `src/compiler/50.mir/mir_target_hir_symbol_writes.spl` (`MirSymbolWriteLedger`) — the 8 writer rows (provider metadata, default bindings/rewrite, resident default globals, native trait conversion/thunks, nested lambda lowerer; alias site opens the task) record each live SymbolTable allocation; `lower_module` resolves per mode (legacy records nothing and is byte-identical; shadow fatal when the owner-order merge differs from the legacy journal; typed uses the merge, conflicts fatal). Evidence: `test/01_unit/compiler/50.mir/mir_target_hir_symbol_writes_spec.spl` 13/13 on the seed; live `array_move_lowering_spec` legacy 58/2 identical before/after (shadow 16/44 identical before/after — all `target_hir_unsupported_arch` from the layout reader on an `unknown`-arch fixture, not this wiring). Rows remain `pending-stage3`: (a) no seed-run spec reaches the 8 writers with a non-legacy mode, so flipping needs a self-hosted Stage-3 shadow run with zero `target_hir_symbol_writes_*` errors; (b) typed does not yet READ through the overlay — the live table stays authoritative; (c) owner decision needed: allocation names embed `next_symbol_id` (`__mir_default_{id}_…`, `__mir_default_global_{id}`), so overlay values are allocation-order dependent and owner-order merge alone cannot make parallel output deterministic.
Recommended flag semantics (names **proposed**, not asserted to exist):

```text
SIMPLE_TARGET_HIR_MODE=legacy|shadow|typed
SIMPLE_TARGET_HIR_VERIFY=0|1
SIMPLE_TARGET_HIR_STORAGE=auto|dense|sparse
```

`shadow` computes and verifies the new resolution against the existing path but continues publishing existing output; it must have bounded memory and time. These flags are development/config controls, not semantics of a language program or cache key unless they can affect output.

**Release ordering:** Structural P1–P8 fits below the preexisting cache execution order **S1 asynchronous compile nodes/I/O → S2 shared compiler API/invoker → S3 pseudo-immutable storage**, unless independently proven narrow preparatory changes can land without claiming S3 behavior. Do not flip the per-file path on merely because TargetHIR is available.

## 9. Acceptance test and formal verification matrix

### 9.1 New SSpec/acceptance cases

| ID | Test | Expected result |
|---|---|---|
| IHIR-01 | HIRBuilder alias tries to modify child Dict/list after freeze | Mutation forbidden or a private detached copy; published HIR unchanged |
| IHIR-02 | `NotInit<HirNode>` or missing required type/layout obligation reaches freeze | Named construction/validation error; no Ready state |
| IHIR-03 | Two target workers read one HIR snapshot while third attempts mutation | All readers see exact identical root; mutation prohibited |
| IHIR-04 | Raw HirModule passed into target-only MIR entrypoint | Compiler type error once strict API enabled |
| IHIR-05 | IDs from another module/arena/region reused | Rejected rather than silently indexing same integer |
| IHIR-06 | HIR parent evicted while target worker suspended | Lifetime pin keeps memory valid; no stale pointer/ABA |
| THIR-01 | Same HIR to Linux x86_64 and Windows x86_64 | Shared portable semantics only; distinct ABI/runtime layout when required |
| THIR-02 | x86_64 vs AArch64 vs RV64 and RV32 | Correct pointer width, alignment, endian and ISA legalizations |
| THIR-03 | SimpleOS vs Linux same CPU | Correct sosix backend, runtime/OS availability and object compatibility |
| THIR-04 | `@when` changes parse/import/export/type/diagnostic | Distinct constrained semantic HIR or verified shared subgraph; no stale portable hit |
| THIR-05 | Target negative query flips, feature becomes available | Read witnesses force invalidation/alternative resolution |
| THIR-06 | SIMD capability or inline-asm match changes | Correct arm/legalization or named unsupported/exhaustiveness error |
| THIR-07 | Sparse overlay entry missing | Explicit obligation failure, never a default/native host result |
| THIR-08 | Different HIR generation or target fingerprint reuses an overlay key | Rejected; new overlay created safely |
| THIR-09 | Same-key concurrent target region requests | One accepted producer; awaiters receive same immutable result |
| THIR-10 | Race at publish/cancel/retry and weak-memory reader | No lost wakeup, partial ready, stale generation or double publish |
| TMIR-01 | Legacy and typed-view MIR paths over representative existing variants | Equivalent diagnostics, CFG/SSA/ABI semantics and deterministic output bytes when supported |
| TMIR-02 | HIR expr/stmt/type transition coverage | Missing arms fail, unsupported arms emit their named diagnostics, no silent wildcard |
| TMIR-03 | Generic enum/Result/Option payload, ctor defaults, method receiver and borrowed-owner path | No regressions in known sensitive semantic/ABI/ownership families |
| TMIR-04 | Active transient scope and final-body/archive digest validation | TargetHIR never bypasses or outlives borrowed HIR authority |
| CACHE-TH-01 | Warm final OBJ/BIN hit | Zero TargetHIR/MIR work; cached final artifact materialized/validated only |
| CACHE-TH-02 | Different CPU changes only codegen tuning (semantics unchanged) | Same admitted HIR; invalidation only at actually affected stages |
| CACHE-TH-03 | Source/TLDR, macro/AOP, `.rr` or negative import changes | Correct dependent artifacts invalidated, including directory membership changes |
| CACHE-TH-04 | Missing/old/corrupt HIR or overlay codec record | Reject/migrate explicitly; no automatically portable fallback |
| PERF-TH-01 | One/four/eight targets, dense vs sparse, cold vs warm | Captured p50/p95, CPU/RSS/allocs, per-stage hit and resolution counts |

Extend corresponding executable `test/01_unit`, `test/02_integration`, `test/03_system`, documentation SSPEC and compiler-schema transition registries, following the repository's existing source-to-spec layout. Preserve older HIR-01…06, EQ-01…04, SLOT-01…06, LIFE-01…03, BIN-01…04 and cache/SCV test identities; the new cases are additive.

### 9.2 Formal obligations

For any published `HirSnapshot H`, target `T`, frozen `TargetHIR R`, and MIR worker `W`:

1. **Deep immutability:** `freeze(H)` implies all reachable semantic payloads are read-only for every valid reader lifetime.
2. **Parent identity:** `R.parent_id = H.id` and every resolved node ID belongs to `H` and its declared region.
3. **Target soundness:** every target observation in `H` and `R` is satisfied by normalized `T` or resolved to a named error; semantic-variant selection is deterministic.
4. **Completeness:** each operation marked as requiring ABI/layout/endian/ISA has a verified resolved value before target-dependent MIR emission.
5. **Publication atomicity:** `Ready(R)` exposes a fully constructed immutable payload; canceled/failed builders cannot publish a successful result.
6. **Cache soundness:** equal admitted keys and required witness closure imply observationally equivalent artifacts; missing/unknown witness broadens invalidation or causes a miss.
7. **Lifetime safety:** valid pins keep HIR/overlay storage alive through MIR consumption, eviction, compaction and cancellation.
8. **Noninterference:** `lower(H, T1)` and `lower(H, T2)` cannot change `H` or each other's inputs, regardless of task ordering.
9. **Transition coverage:** every admitted HIR expression/statement/type arm has exactly one supported or explicit rejected lowering disposition.
10. **Bootstrap parity:** legacy and new interfaces agree on all previously admitted fixtures before switching the default.

Lean/model-checking must be paired with executable mutation, alias, cache-corruption, concurrency and native target tests. A model of the state machine is not proof that a real semantic read set was complete.

## 10. Rollback, ownership and completion definition

- **Rollback:** Keep old MIR lowering route and previous cache schema available during staged qualification; rollback must discard new TargetHIR cache entries by schema/version without invalidating unrelated valid HIR/OBJ artifacts. Never silently decode a new record as an old one.
- **Ownership:** HIR package owns semantic freeze and node IDs; `target_hir` owns target resolution and private table layout; MIR package owns lowerer scratch; driver owns target request normalization and exact source/body admission; SCV owns snapshot/witness evidence; TaskRunner owns concurrency/admission; backend owns object format and machine code.
- **No new fake completion evidence:** `P0–P8` are proposals until tested. A passing source-level shape spec alone is insufficient; actual compiled Simple/compiler, Stage 3 native, and multi-target execution/ABI results are required.
- **Exit:** Single-target overhead within agreed budget, multi-target shared-HIR benefit demonstrated, low peak RSS relative to full per-target copies, zero cross-target contamination, correct binary/cache and SCV invalidation, bootstrap and supported backend/CI matrix qualified, no raw mutable-HIR bypass left on strict MIR path.

## 11. First concrete PR sequence (minimal disruption)

1. **PR-A (no functional change):** Inventory test and `HirSnapshotId`/`TargetHIR` types with read-only facades; record all existing MIR lowerer entrypoints and preserve source specs.
2. **PR-B:** Deep-freeze ownership and canonical snapshot ID on the admitted existing HIR path, with alias/mutation tests. Initially no overlay and no MIR switch.
3. **PR-C:** `TargetHIRBuilder` resolves only type-layout/ABI for a narrow module/region. Store immutable dense/sparse resolution and test two targets against identical HIR.
4. **PR-D:** Migrate one MIR reader family through the typed facade (e.g., inline asm target guard or layout), with shadow equivalence; keep the existing `MirTargetContext` adapter.
5. **PR-E:** Integrate region readiness and target-resolution cache identities with the existing archive owner, transient lifetime and SCV validation; test cold/warm/failure concurrency.
6. **PR-F:** Extend field/ABI/SIMD/generic consumers, update generated transition/codec specs, then qualify Stage 3 native path and profile.

Do not merge a large mechanical rename of every `Hir*` type, move all functions at once, or change the release default before the native qualifier exists.

## 12. Sources and inspection limitations

### Existing project design files reviewed

- `simple_cache_async_build_final_design_2026-10-26.md` (user's prior saved design, §§4, 7, 8, 20)
- `simple_cache_with_scv_implementation_plan_2026-10-27_sosix_rr_updated.md` (user's updated saved plan, especially §§12, 19, 31–32)
- `simple_tldr_generic_aspect_macro_cache_plan_2026-10-24.md`
- Repository `doc/03_plan/compiler/phase3_incremental_build_completion_2026-10-13.md`
- Repository `doc/03_plan/compiler/driver/hir_mir_lowering_unstub_project.md` (historical proposal, not present-state proof)
- Repository `doc/06_spec/01_unit/compiler/mir/mir_target_context_wiring_source_spec.md`
- Repository `spec/compiler_schema/transitions/hir_expr_to_mir.sdn`, plus related stmt/type transition contract names

### Primary implementation references

- [`HirModule` and SymbolId declarations](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_types.spl)
- [`HirFunction`, layout, generic and target-related declarations](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_definitions.spl)
- [`HIR codec and canonical admission guards`](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/hir_codec.spl)
- [`MirTargetContext`](https://github.com/ormastes/simple/blob/main/src/compiler/00.common/mir_target_context.spl)
- [`MirLowering` mutable state](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/mir_lowering_types.spl)
- [`MIR module lowering`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/module_lowering.spl)
- [`Inline asm target selection`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/asm_and_targets.spl)
- [`Borrowed archived HIR admission before MIR`](https://github.com/ormastes/simple/blob/main/src/compiler/50.mir/_MirLowering/archive_borrowed_module_v1.spl)
- [`HIR expression transition schema`](https://github.com/ormastes/simple/blob/main/spec/compiler_schema/transitions/hir_expr_to_mir.sdn)

### External compiler references

- LLVM [Target-Independent Code Generator](https://llvm.org/docs/CodeGenerator.html) and [Writing an LLVM Backend](https://llvm.org/docs/WritingAnLLVMBackend.html): distinguish target-independent IR from machine-specific lowering and data layout.
- Rust compiler [Memory management](https://rustc-dev-guide.rust-lang.org/memory.html): arena allocation and shared IR references.
- MLIR [Attributes and Types](https://mlir.llvm.org/docs/DefiningDialects/AttributesAndTypes/): immutable, shared interned storage precedent.
- LLVM [Programmer's Manual](https://llvm.org/docs/ProgrammersManual.html): indexed arrays versus dense/small map tradeoffs.
- Clang [ThinLTO](https://clang.llvm.org/docs/ThinLTO.html): independent parallel backend/cache work without monolithic whole-program memory.

**Evidence boundary:** No local Simple checkout was present in the working directory. Current-source snippets came from authenticated GitHub file reads and code search. Prior plans came from the user's saved documents. No compiler, test suite, native bootstrap, performance benchmark, or cache migration was run. Detailed implementation feasibility and actual speed/memory benefits remain unverified until P0 and the subsequent acceptance gates.

---

## Local adoption note — 2026-11-03 KST

The text above preserves the user's supplied plan and its original authoring status and evidence boundary. Those historical statements are not claims about the local adoption session.

The user explicitly requested applying this plan. It is adopted as the governing design for the isolated foundation worktree `/tmp/simple-targethir-foundation-20261103`, starting at release revision `4fccb94e564b25a0a2effdd711113da5a1b1e20c`. P0 is an inventory/baseline phase with no compiler source writes. PR-A and subsequent phases retain their distinct completion gates; saving this document does not complete any implementation or qualification phase.

The earlier host-view work in `/tmp/simple-hir-host-view-20261103` remains an unmerged experimental draft. Its review is saved at `/tmp/simple-hir-host-view-20261103/doc/09_report/hir_host_view_review_20261103.md`. Its default strict routing, whole-closure preparation, codec-dependent view admission, and shallow read-only payload assumptions are not accepted as compliance with this plan's staged rollout, region readiness, deep immutability, and no-whole-program-barrier requirements. No compiler source from that draft was copied while saving this document.

This document-saving task executed no compiler, native test, bootstrap, benchmark, or cache migration. Runtime, concurrency, memory-safety, performance, and rollout claims require the plan's specified evidence. The earlier cross-compilation and release work remains subject to its existing exact-candidate verification and review gates; this adoption note does not waive them.
