# Simple MDSOC+ Tagged Structural Compute Architecture

**GPU/SIMD/CPU parser, AOP and optimization mutation, Clang bridge, DOM/CSS mutation, HTML layout, linker/resolver, and SSD-backed object placement**

**Date:** 2026-07-31
**Status:** Proposed architecture and parallel implementation plan
**Repository baseline:** `ormastes/simple` current `main` as inspected on 2026-07-31
**Supersedes:** *Simple GPU Compiler Substrate: Research, Architecture, and Implementation Plan*
**Related plans:**
- per-lane parallel plans: `doc/03_plan/platform/structural_compute/` (parser framework, Clang bridge, HTML/CSS parser, layout framework, web layout manager, link manager, GPU MMU/Object VM, WebRender GPU offload)
- experimental GPU web lane: `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — consumes this document's QueryIR/TagMap/MutationIR/Object VM contracts; its `GpuWebScene` device pools are Object VM-managed arenas under Part VIII placement/lease rules
- conservative production render plan: `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md` (unchanged by this document)

---

## 0. Executive decision

The previous design should be extended into a **tagged structural-compute platform** rather than adding independent AOP, optimizer, Clang, HTML, CSS, layout, linker, and GPU-memory implementations.

The platform has six shared layers:

```text
1. structural_core
   stable identity + TagMap + provenance MappingGraph + QueryIR
   + MutationIR + dependency/invalidation

2. parse_framework
   lexer/structural parser/grammar/action programs
   + incremental parse + tag/mapping emission

3. resolve_framework
   generic definition/reference/constraint resolution
   specialized by SMF linker, Clang offload linker, and Web resource/style resolver

4. spatial_layout
   DOM/style -> formatting-context graph -> layout fragments

5. execution_framework
   CPU reference, adaptive SIMD/GPU hybrid, GPU-resident modes
   + deterministic scheduling + verification + fallback

6. object_placement
   stable object handles + VRAM/host/SSD placement + leases
   + content-addressed persistence + bounded host-memory transport
```

All domain implementations consume these shared contracts:

```text
Simple compiler   Clang/LLVM bridge   HTML/CSS/DOM   Web renderer
      \                  |                 |              /
       \                 |                 |             /
        +----- QueryIR / TagMap / MappingGraph --------+
        +----- MutationIR / InvalidationGraph ---------+
        +----- ExecutionPlan / PlacementPlan ----------+
```

### Mandatory architectural separations

1. **Residency placement is not HTML layout.**
   - `ResidencyPlacement` decides where an arena resides: SSD, host, pinned host, shared device memory, or local VRAM.
   - `SpatialLayout` decides where a rendered box or fragment appears in document coordinates.

2. **A binary linker is not a browser layout engine.**
   - They may share sorting, grouping, graph resolution, placement planning, receipts, and object storage.
   - They use different domain profiles and cannot share domain semantics.

3. **Tags are not fields added to every AST or DOM node.**
   - Tags live in typed side tables keyed by stable entity IDs.
   - Dense tags use columns or bitsets; sparse tags use sorted records and inverted indexes.

4. **Mutation is never an unverified in-place callback.**
   - A transformation emits a deterministic `MutationPlan` against an immutable snapshot.
   - Validation, conflict resolution, invalidation, provenance update, and commit are explicit stages.

5. **GPU-resident does not mean CPU-free.**
   - It means eligible bulk data and bulk stages remain resident on the GPU and do not round-trip through host RAM.
   - Security policy, transaction commit, unsupported semantics, diagnostics, and recovery remain bounded host-control responsibilities.

### Three execution modes

Every parser, compiler stage, linker, style engine, layout manager, and renderer supports the same semantic modes:

```text
cpu_reference
    Current/no-GPU path; correctness oracle; may use ordinary scalar CPU code.

hybrid_vector_gpu
    CPU controls ordered/irregular work; SIMD and GPU execute profitable bulk work.

resident_gpu
    Canonical arenas, indexes, and intermediate results remain device-resident;
    CPU performs only control, unsupported fallback, security, and commit work.
```

`auto` may choose one of these three modes per stage, but it is a policy selector rather than a fourth semantics mode.

---

## 1. Scope, goals, and non-goals

### 1.1 Goals

The architecture must support:

- parser-produced tags and mappings for AOP, optimization points, diagnostics, source links, CSS selectors, DOM nodes, layout fragments, linker symbols, and final output ranges;
- one compiled structural-query model for Simple pointcuts, optimizer selection, Clang AST matching, LLVM IR matching, DOM queries, CSS selectors, and linker symbol queries;
- transactional source, AST, HIR, MIR, LLVM IR, DOM, CSSOM, style, layout, and linker mutations;
- exact dependency and invalidation propagation after source, DOM, CSS, profile, or resource changes;
- three execution modes with deterministic output and CPU fallback;
- nearly project-size-independent host RAM usage through SSD-backed immutable artifacts and bounded staging;
- parallel implementation by multiple agents with frozen interfaces and non-overlapping ownership;
- MDSOC+ integration without creating a source-directory cross-product for mode, target, storage, and assurance dimensions.

### 1.2 Non-goals for the first production release

- a complete production C++ preprocessor, parser, template system, concepts engine, and Sema entirely rewritten as GPU kernels;
- a fully parallel browser-compatible WHATWG tree builder that permits parser-blocking scripts to mutate the input stream without an ordered commit stage;
- transparent SSD-backed raw GPU pointers that may fault at arbitrary instructions;
- one GPU allocation descriptor per token, AST node, DOM node, style record, or MIR instruction;
- arbitrary third-party mutation callbacks with unrestricted pointers into compiler or renderer state;
- replacing current CPU implementations before parity, fault-recovery, and cost-model gates pass.

---

## 2. Current Simple baseline and architectural gaps

### 2.1 Compiler and MDSOC baseline

The current compiler is already organized into numbered layers, including frontend, HIR, MIR, MIR optimization, backend/linker, driver, MDSOC, tools, interpreter, and loader. The existing MDSOC implementation provides feature-stage ports and stage-boundary transforms. This is the correct integration point; the new platform must extend it rather than create a parallel compiler driver.

Important current assets:

- `src/compiler/10.frontend/`: lexer, parser, AST, desugaring, syntax-level optimization grouping;
- `src/compiler/60.mir_opt/`: MIR optimizer and dynamic optimizer manifests;
- `src/compiler/70.backend/`: code generation and linker;
- `src/compiler/85.mdsoc/`: feature ports, transforms, adapters, and virtual capsules;
- `src/compiler/90.tools/`: AOP and tooling surfaces.

### 2.2 AOP gap

Simple already has:

- `pc{...}` pointcut syntax;
- before, after-success, after-error, and around advice;
- join-point concepts for execution, calls, assignments, decisions, conditions, and errors;
- MIR-level weaving support and runtime advice support.

The principal architectural gaps are:

- pointcut matching is partly duplicated across interpreter and compiler paths;
- some selectors are parsed but not semantically matched in the core path;
- pointcuts operate primarily on text and ad hoc context rather than stable entity IDs, typed tags, and structural indexes;
- weaving is not yet expressed as a general transaction with explicit read/write sets, provenance, invalidation, and conflict rules.

### 2.3 Optimizer gap

The optimizer already has:

- static/dynamic/both application modes;
- source/MIR/both scopes;
- pass cost classes;
- backend policies and capability requirements;
- a versioned dynamic-pass manifest.

The main gap is that source selection can still degrade to line-oriented text-pattern matching. The platform should replace that with structural queries over canonical syntax, semantic, and MIR indexes while preserving the existing pass manifest, cost, and backend-selection concepts.

### 2.4 Parser memory gap

The repository's parser-memory investigation correctly identifies the following as unacceptable for the target architecture:

- one heap text object per source character;
- copied token and AST strings;
- arena lengths reset without reclaiming element objects;
- cross-file accumulation of frontend objects.

The GPU work therefore begins only after canonical flat source buffers, span tokens, interned strings, index-based SoA nodes, and stage-bounded arena lifetimes exist. Moving an object-heavy parser unchanged to VRAM would merely move the memory defect.

### 2.5 Browser gap

The browser already has:

- a canonical DOM/render-session direction;
- revisions for document, style, resources, viewport, and composition;
- a flat child index and SoA-like layout result arrays;
- bounded HTML/CSS/resource admission;
- retained style/layout/paint state as an architectural goal.

The current implementation still has two limitations relevant here:

- `HNode` and `Style` are object-heavy and contain many owned text values or mutable fields;
- DOM and stylesheet changes may conservatively invalidate parse, CSS, style, layout, and paint, rather than calculating exact affected nodes and stages.

### 2.6 Linker gap

The custom SMF path cannot be replaced by mold because mold targets native object formats rather than SMF. The appropriate route is:

- keep existing native linker selection for ELF/Mach-O/PE;
- implement the new parallel/GPU linker first for SMF;
- share generic graph-resolution primitives with other domains without conflating their semantics.

---

## 3. Research findings that shape the design

### 3.1 Parser research

SIMD structural parsing demonstrates that a parser can separate byte classification and structural-index production from later semantic construction. GPU parser research demonstrates that each chunk can summarize its lexical state transition and that the summaries can be composed by scans, avoiding a serial pass over the entire source. These findings justify a parser framework with separate lexical, structural, grammar, and action programs.

### 3.2 Clang and LLVM research

Clang provides several relevant extension layers:

- LibTooling and `FrontendAction` for translation-unit processing;
- AST Matchers for declarative AST selection and capture;
- the Transformer framework for source-to-source edits;
- LLVM pass plugins through `PassBuilder` extension points;
- pass instrumentation callbacks before and after passes;
- structured optimization remarks and debug/provenance metadata.

These interfaces make a Clang bridge realistic, but the bridge should pin a supported LLVM/Clang version because internal AST and tooling APIs are not a stable long-term ABI.

AspectC++ and Clava demonstrate practical Clang-based source-to-source AOP and programmable AST transformations. The design should borrow their separation of selection, capture, and transformation while using Simple's own QueryIR, MutationIR, and provenance model.

### 3.3 Browser research

Browser-compatible HTML construction is inherently ordered and stateful: tokenization feeds tree construction, which mutates document state and may interact with scripts. Consequently, the first GPU HTML path should accelerate tokenization, attribute extraction, indexes, and speculative structure while retaining an ordered tree-builder commit.

Modern browser style engines compile selector features into invalidation indexes. DOM changes schedule only potentially affected nodes or subtrees, after which computed-style differences decide whether layout, paint, or compositing is necessary. This is the model Simple should adopt instead of using a single full-pipeline dirty flag.

Parallel layout research shows that formatting contexts and tree subproblems can be parallelized, but browser workloads are not uniformly large enough to offset scheduling and synchronization overhead. Layout must therefore use per-island cost estimation rather than unconditional GPU dispatch.

### 3.4 GPU memory and storage research

GPU virtual-memory APIs separate address reservation, physical allocation, mapping, and access rights. GPUDirect Storage can move data directly between compatible storage and GPU memory. Research systems such as BaM, GPUfs, and ActivePointers demonstrate GPU-managed caches, GPU-initiated storage access, and software translation.

The portable Simple contract should still be explicit object residency rather than transparent page faults:

- stable object handles;
- lease-bound resident views;
- miss queues and continuation batches;
- mandatory bounded staging backend;
- optional direct-storage backend;
- experimental device-initiated backend.

---

# Part I — Shared structural platform

## 4. Stable identity model

Every parser, compiler, linker, DOM, CSS, layout, and paint entity needs two identities:

1. a compact, snapshot-local reference for hot loops and GPU kernels;
2. a durable key for caches, source links, diagnostics, manifests, and cross-revision comparison.

### 4.1 Hot reference

```simple
struct EntityRef:
    object_slot: u32
    local_index: u32
```

`object_slot` resolves through the Object VM descriptor table. The descriptor includes object generation, schema, snapshot epoch, and residency state. `local_index` addresses an element inside an arena.

Properties:

- exactly 64 bits in hot arrays;
- no embedded raw address;
- valid only while the referenced snapshot/object lease is valid;
- one object descriptor may cover millions of nodes.

### 4.2 Durable entity key

```simple
struct EntityKey:
    artifact: ArtifactId
    schema: EntitySchemaId
    local_identity: u64
```

`ArtifactId` is content-addressed and includes the relevant parser/compiler/layout schema version. `local_identity` may be a node index, symbol ID, rule ID, section ID, or stable generated ordinal.

`ArtifactId` and `Hash128` were referenced throughout this section but never
given a definition; both are ratified here so producers cannot disagree on
width or field order:

```simple
struct Hash128:
    hi: u64
    lo: u64

struct ArtifactId:
    content_hash: Hash128
    schema_version: u32
```

`hi` is the more significant half. Both halves are u64 bit patterns carried in
i64, so a hash with the top bit set appears negative; that is expected and
round-trips exactly. `schema_version` is the parser/compiler/layout schema the
artifact was produced under, which is what lets a durable key resolve only
against a compatible producer (§30.1).

`EntitySchemaId` above is a `u32`. Every scalar in this section is a fixed-width
unsigned integer of the declared width, encoded little-endian, and writers mask
to that width so an out-of-range value cannot silently widen a record.

A durable source-level declaration may also include a semantic key:

```simple
struct SemanticEntityKey:
    language: LanguageId
    qualified_name: StringId
    signature_hash: Hash128
    definition_artifact: ArtifactId
```

This permits cross-revision matching without assuming that old node indexes remain valid.

### 4.3 Source anchor

```simple
struct SourceAnchor:
    file: ArtifactId
    byte_start: u32
    byte_end: u32
    spelling_context: ExpansionContextId
    expansion_context: ExpansionContextId
```

For Simple, the two contexts are normally the same. For Clang, both macro spelling and macro expansion locations are required. Line and column are derived presentation data, never the authoritative identity.

### 4.4 Snapshot and revision

```simple
struct SnapshotId:
    root_artifact: ArtifactId
    epoch: u64

struct RevisionPair:
    before: SnapshotId
    after: SnapshotId
```

A mutation always targets one immutable `SnapshotId` and produces another. A stale mutation plan fails instead of silently modifying a newer state.

---

## 5. Typed TagMap framework

### 5.1 Purpose

`TagMap` is the shared extension mechanism for:

- AOP join-point categories and pointcut attributes;
- optimizer points, vectorization suitability, hotness, and missed reasons;
- compiler effects, ownership, safety, and target capabilities;
- Clang AST categories and LLVM metadata;
- DOM state, attributes, pseudo-state, and mutation categories;
- CSS selector features and property categories;
- style/layout/paint invalidation;
- linker visibility, binding, reachability, and section properties;
- memory placement, affinity, recomputability, and persistence.

### 5.2 Tag schema

```simple
struct TagKey:
    namespace: StringId
    name: StringId
    value_type: TagValueType
    cardinality: TagCardinality
    lifetime: TagLifetime
    merge_policy: TagMergePolicy
    authority: TagAuthority

struct TagSchema:
    version: u32
    keys: [TagKey]
```

```simple
enum TagValueType:
    Marker
    Bool
    I64
    U64
    F64
    StringId
    EntityRef
    ArtifactId
    SourceAnchor
    SmallSet

enum TagLifetime:
    Snapshot
    Stage
    Artifact
    ProfileSession
    DiagnosticOnly

enum TagMergePolicy:
    Replace
    Union
    AppendStable
    Max
    Min
    ErrorOnConflict

enum TagCardinality:
    One
    Optional
    Many

enum TagAuthority:
    Parser
    Semantic
    Analysis
    Profile
    External
    Policy
```

`TagCardinality` and `TagAuthority` were declared in `TagKey` but left
unenumerated in the original draft; they are ratified above so no two lanes
invent conflicting vocabularies. Both are one `u8` at a frozen `TagKey` offset,
so extending either is a tagmap-schema minor bump that does not disturb the
surrounding layout.

- `TagCardinality` is the minimum set the §5.3 storage table actually
  distinguishes: a dense scalar column (`One`), a sparse marker/value record
  (`Optional`), and an offset/count small multi-value set (`Many`).
- `TagAuthority` mirrors the producer families implied by the §5.5 namespace
  policy: `syntax.*`/`source.*` from the parser, `semantic.*` from resolution,
  `opt.*`/`aop.*`/`link.*` from analysis passes, `profile.*` from a profiling
  session, `clang.*`/`llvm.*` from an external bridge, and
  `placement.*`/`security.*` from explicit policy.

### 5.3 Storage representations

The storage representation is selected per tag key:

| Tag shape | Representation | Example |
|---|---|---|
| dense marker | bitset | `dom.is_element`, `mir.is_call` |
| dense scalar | parallel column | block frequency, style ID |
| sparse marker/value | sorted `(EntityRef, value)` records | `aop.attr`, `opt.reason` |
| inverted query index | sorted entity lists by key/value | class, ID, tag name, symbol name |
| small multi-value set | offset/count into value arena | effects, advice categories |

There is no per-node dictionary and no general heap allocation during matching.

### 5.4 API

```simple
interface TagReadPort:
    fn has(entity: EntityRef, key: TagKeyId) -> bool
    fn get(entity: EntityRef, key: TagKeyId) -> TagValue?
    fn values(entity: EntityRef, key: TagKeyId) -> TagValueRange
    fn entities(key: TagKeyId) -> EntitySetView
    fn entities_equal(key: TagKeyId, value: TagValue) -> EntitySetView

interface TagWritePort:
    fn emit(entity: EntityRef, key: TagKeyId, value: TagValue)
    fn emit_marker(entity: EntityRef, key: TagKeyId)
    fn remove(entity: EntityRef, key: TagKeyId)
    fn finish() -> TagShardRef
```

`TagValue` appears throughout these signatures but was never defined. It is
ratified as a discriminated payload — `value_type` selects which field carries
the value, and the other fields are unused for that variant:

```simple
struct TagValue:
    value_type: TagValueType
    num: u64
    ref: EntityRef
    artifact: ArtifactId
    anchor: SourceAnchor
```

| `value_type` | payload field |
|---|---|
| `Marker` | none |
| `Bool`, `I64`, `U64`, `F64`, `StringId` | `num` |
| `EntityRef` | `ref` |
| `ArtifactId` | `artifact` |
| `SourceAnchor` | `anchor` |
| `SmallSet` | `num` — arena offset in the low 32 bits, count in the high 32 |

Two consequences worth stating so producers do not each rediscover them:

- For `F64`, `num` carries the raw IEEE-754 bit pattern, not an `f64`. Simple
  has no f64 bit-level reinterpret today — the same pre-existing gap already
  recorded in `src/lib/common/encoding/cbor.spl` and `bson.spl`. The 8-byte wire
  slot is frozen and correct and a Rust/C++ producer can populate it now; the
  Simple-side conversion unblocks when that already-filed runtime request lands.
- The `SmallSet` offset/count pair must be packed at 64-bit width. Packing it
  from `u32` operands evaluates `count << 32` at 32-bit width and silently
  discards the count.

### 5.5 Namespace policy

Recommended namespaces:

```text
syntax.*       lexical/syntactic facts
semantic.*     resolved symbols, types, effects
source.*       source anchors and generated/expanded status
aop.*          join points, attributes, advice eligibility
opt.*          optimization points, legality, profitability, remarks
profile.*      hotness, counts, latency, cache misses
clang.*        Clang AST/PP/Sema classifications
llvm.*         LLVM operation/metadata classifications
dom.*          node kind, attributes, state, structural features
css.*          selector/declaration/property features
style.*        cascade and computed-style categories
layout.*       formatting contexts, dependencies, dirty reasons
paint.*        display-list and damage categories
link.*         definitions, references, bindings, sections, relocations
placement.*    tier, affinity, reuse, persistence, recomputability
security.*     trust domain, taint, capability, validation state
```

### 5.6 Zero-overhead inactive path

The parser and compiler should not emit every optional tag unconditionally. `TagDemand` is calculated from enabled consumers:

```simple
struct TagDemand:
    required_keys: TagKeySet
    required_indexes: TagIndexSet
    source_mapping_level: MappingLevel
```

When AOP, optimization diagnostics, LSP, or profiling is disabled, the demand set excludes those tags and no corresponding columns or indexes are allocated.

---

## 6. MappingGraph and provenance

### 6.1 Why mappings must be many-to-many

Compiler and renderer transforms routinely split, merge, clone, inline, fold, or synthesize entities:

- one source expression lowers to several MIR instructions;
- several expressions fold into one constant;
- an inline operation clones a callee body into many call sites;
- advice inserts instructions around an existing join point;
- one CSS rule matches many DOM nodes;
- many declarations contribute to one computed style;
- one DOM node creates multiple layout fragments;
- several input sections contribute to one output range.

A single `source_node` pointer or line number is insufficient.

### 6.2 Mapping edge

```simple
struct MappingEdge:
    from: EntityRef
    to: EntityRef
    kind: MappingKind
    transform: TransformInstanceId
    flags: MappingFlags
    weight_milli: u16
```

```simple
enum MappingKind:
    ParsedFrom
    ExpandedFrom
    DesugaredFrom
    ResolvedFrom
    LoweredFrom
    ClonedFrom
    InlinedFrom
    WovenFrom
    OptimizedFrom
    GeneratedFrom
    LinkedFrom
    Styles
    CascadesInto
    LayoutOf
    PaintOf
    HitRegionOf
    InvalidatedBy
```

`weight_milli` is optional diagnostic attribution, not semantic correctness. For example, a merged optimized instruction may attribute 600/400 to two inputs.

`TransformInstanceId` and `MappingFlags` are declared as `MappingEdge` fields
but were never defined; both are ratified here so lanes cannot disagree on a
width or on what a bit means.

`TransformInstanceId` is a `u32`, applying the scalar convention already
ratified in §4.2 — a fixed-width unsigned integer, little-endian, and `u32` for
an identity scalar unless a section says otherwise. The identifier occurs
exactly once in the repository, at that field declaration, so nothing else
constrained it.

`MappingFlags` is a `u32` bitfield with three defined bits. Each bit exists
because a sentence in this chapter is otherwise unrepresentable, not because a
producer wanted somewhere to put a hint:

| Bit | Name | Sentence that forces it |
|---|---|---|
| 0 (`0x1`) | `WEIGHT_VALID` | §6.2 above: `weight_milli` is *optional*. Without the bit, an edge attributing 0/1000 and an edge supplying no attribution encode to identical bytes |
| 1 (`0x2`) | `SYNTHETIC` | §6.5 `Synthesize`, and §6.1 "or synthesize entities" — the target has no true source origin, which is part of why §6.1 rejects a single source pointer |
| 2 (`0x4`) | `DISCARDED` | §6.5 `DiscardWithReason` plus "A pass cannot silently drop origins" — a dropped origin not recorded as an edge *is* the silent drop that rule forbids |

An edge without `WEIGHT_VALID` attributes a full share, 1000 milli: a merged
instruction with no stated split still fully derives from each listed input.

Bits 3..31 are reserved and must be zero. A set reserved bit is a hard reject,
exactly as an unknown enum discriminant is — a reader that masked one off would
report success on provenance written by a producer it does not understand.

### 6.3 Storage

Mappings are stored as compressed sparse adjacency structures:

```text
from_offsets[]
from_edges[]
reverse_offsets[]    # built only when demanded
reverse_edges[]
```

A stage can emit forward edges cheaply and construct the reverse index lazily.

The element type of `reverse_edges` was never stated. It is a `u32` **index into
the forward edge list**, not a duplicated edge record: this section calls the
structure the reverse *index* and requires it be cheap to build lazily, and a
second copy of every edge body is neither cheap nor guaranteed to agree with the
first.

The four arrays are a compressed sparse row (CSR) layout, and a CSR is
undecodable without its well-formedness rules — without the terminator rule
alone, `N` versus `N + 1` offset entries is ambiguous. The invariants below are
therefore normative, and are enforced identically on encode and decode so no
lane can emit a shard another lane must reject:

- `from_offsets` has `node_count + 1` entries, starts at 0, is non-decreasing,
  and ends at the edge count. Edges for node `n` are
  `from_offsets[n] .. from_offsets[n + 1]`.
- `reverse_offsets` obeys the same rule against the `reverse_edges` length.
- every `reverse_edges[i]` is less than the edge count, and the reverse index is
  no longer than the edge list. A *shorter* reverse index is legal: a lazily
  built partial index does not cover targets outside its reverse node range.
- when the reverse index is absent, both reverse arrays are empty.
- no trailing bytes, and no edge carrying a reserved `MappingFlags` bit.

A producer must not be able to put a corrupt CSR on the wire, so an ill-formed
shard encodes to an empty buffer rather than to bytes no decoder will accept.
This matters more here than for any other structure in this document: a
corrupted offset array does not fail loudly, it silently returns a *neighbouring
node's* provenance — and provenance that is wrong-but-plausible is exactly what
§6.5 forbids.

### 6.4 Mapping API

```simple
interface MappingReadPort:
    fn forward(entity: EntityRef, kind_mask: MappingKindSet) -> EntitySetView
    fn reverse(entity: EntityRef, kind_mask: MappingKindSet) -> EntitySetView
    fn trace_to_source(entity: EntityRef) -> SourceOriginSet
    fn trace_to_output(entity: EntityRef) -> EntitySetView

interface MappingWritePort:
    fn map(from: EntityRef, to: EntityRef, kind: MappingKind)
    fn map_many(from: EntitySetView, to: EntityRef, kind: MappingKind)
    fn map_split(from: EntityRef, to: EntitySetView, kind: MappingKind)
    fn finish() -> MappingShardRef
```

`MappingKindSet` is passed as `kind_mask` to `forward` and `reverse` but was
never defined. It is ratified as a `u32` bitset in which bit *i* is `MappingKind`
discriminant *i*. The parameter is named a *mask*, and §6.2 enumerates 17 kinds;
17 bits do not fit a `u16`, so `u32` is the smallest fixed width that holds the
frozen enum. Bits 17..31 are reserved and must be zero under the same hard-reject
rule as §6.2's flags — a reader that ignored a set reserved bit would silently
answer a query about kinds it does not know.

A consequence worth stating rather than rediscovering: adding an 18th
`MappingKind` is a breaking change to `MappingKindSet`, not an additive one, and
requires a schema-version bump.

CORRECTED 2026-08-02. This section used to defer three types in these
signatures as "deliberately not frozen ... tracked open gaps": `MappingShardRef`,
`SourceOriginSet` and `EntitySetView`. Two of the three have since been frozen
and implemented by the groups this section handed them to, so the deferral was
stale prose. Current state, verified against the tree rather than against this
document:

- `EntitySetView` — **FROZEN and implemented.** Handed to the QueryIR group,
  which froze it in `doc/05_design/platform/structural_compute/query_contract_v1.md`
  as 13 bytes, `object_slot u32 | offset u32 | count u32 | order u8`, envelope
  magic `SQSV`. Implemented in `src/lib/common/structural/query/` — the struct
  and `EntitySetOrder` in `query_program.spl`, the codec in `query_codec.spl`.
  Measured 2026-08-02 by round-trip: body length 13, framed length 21, all three
  u32 fields survive encode/decode, and a corrupted `order` discriminant or a
  truncated buffer is hard-rejected rather than silently accepted.
- `MappingShardRef` — **FROZEN and implemented.** Handed to the StageReceipt
  group. 52 bytes (`SnapshotId` 28 + `shard_index` u32 + `edge_count` u32 +
  `Hash128` 16, no padding), defined in
  `src/lib/common/structural/receipt/receipt_types.spl` with an encoder, a
  decoder and a result type in `receipt_codec.spl`.
- `SourceOriginSet` — **still open.** Ownership is resolved below (it belongs to
  MAP), but no struct for it exists anywhere in `src/`; it appears only in prose.
  This is the one genuine remaining gap of the original three.

All three are handle and view types rather than parts of the compressed mapping
format, which is why the mapping group did not freeze them itself.

**`SourceOriginSet` ownership is resolved here: it belongs to MAP.** Three
separate freeze waves each examined it and each declined, on three different
grounds — MAP-versus-QUERY looked ambiguous, no receipt field references it, and
§18.2 separates layout from resolution. Each of those is a correct answer to
"is it *mine*?" and none of them is an answer to "whose *only* reference site is
it?". Enumerating the reference sites decides it: `SourceOriginSet` occurs
exactly once in this document, as the return of a `MappingReadPort` method, and
occurs in no QueryIR field, no receipt field and no resolution signature. That is
the identical argument that placed `MappingKindSet` with MAP two paragraphs
above — sole occurrence in a `MappingReadPort` signature — so it must reach the
same owner. Ambiguity between two lanes is not established by neither lane
claiming a type; it is established by two lanes *referencing* it, and only one
does.

Ownership being decided does not by itself make the type freezable, and the
deferral above still stands for a different and narrower reason: three of
`MappingReadPort`'s four methods return `EntitySetView`, and `trace_to_source` is
the fourth. `SourceOriginSet` is that port's return-shape specialised to carry
origin attribution, so it is frozen **in the same wave as `EntitySetView`, by
MAP** — not by whichever lane needs it first. Freezing it before `EntitySetView`
would fix a view representation the other three methods must then match.

### 6.5 Transformation preservation rules

Every transformation declares one policy:

```simple
enum OriginPolicy:
    PreserveOneToOne
    Split
    Merge
    Clone
    Synthesize
    DiscardWithReason
```

A pass cannot silently drop origins. `DiscardWithReason` records a diagnostic or optimization reason such as dead-code elimination.

---

## 7. QueryIR: one engine, multiple dialects

### 7.1 Design decision

Simple pointcuts, optimizer matching, Clang AST selection, CSS selectors, DOM queries, and linker queries should share:

- entity sets;
- typed tags;
- stable traversal and capture;
- deterministic set algebra;
- CPU/SIMD/GPU execution;
- indexing and receipts.

They should **not** share one user syntax. Each domain compiles its syntax into a common QueryIR plus domain-specific operations.

### 7.2 Dialects

```simple
enum QueryDialect:
    Syntax
    Semantic
    Mir
    ClangAst
    LlvmIr
    Dom
    CssSelector
    LinkGraph
    LayoutGraph
```

### 7.3 Core operations

```simple
enum QueryOpKind:
    SeedAll
    SeedKind
    SeedTag
    SeedTagValue
    FilterKind
    FilterTag
    FilterName
    FilterSourceRange
    TraverseParent
    TraverseChild
    TraverseAncestor
    TraverseDescendant
    TraverseSibling
    TraverseMapping
    TraverseReference
    Intersect
    Union
    Difference
    NegateWithinUniverse
    Capture
    StableSort
    Limit
```

Domain extensions include:

```text
compiler:  call-target, use-def, dominance, post-dominance, loop, effect, type
AOP:       execution, call, assignment, decision, condition, error, cflow
CSS:       compound selector, combinator, pseudo-class, specificity, scope
linker:    defines, references, archive-member, relocation-target, reachable
layout:    formatting-context, containing-block, fragment-owner, dependency
```

### 7.4 Program representation

```simple
struct QueryProgram:
    dialect: QueryDialect
    schema_version: u32
    ops: ObjectRef<QueryOpArena>
    constants: ObjectRef<QueryConstantArena>
    captures: ObjectRef<CaptureSchema>
    index_requirements: TagIndexSet
    determinism: QueryDeterminism
```

The GPU representation is an SoA bytecode, not a graph of heap objects.

### 7.5 Execution API

```simple
struct QueryRequest:
    snapshot: SnapshotId
    program: QueryProgramRef
    universe: EntitySetView
    params: QueryParamBlock
    execution: StageExecutionProfile

struct QueryResult:
    entities: ObjectRef<EntitySetArena>
    captures: ObjectRef<CaptureArena>
    diagnostics: ObjectRef<DiagnosticArena>
    receipt: StageReceipt

interface QueryExecutionPort:
    fn compile(source: QuerySource, dialect: QueryDialect) -> QueryProgramRef
    fn execute(request: QueryRequest) -> QueryResult
    fn explain(program: QueryProgramRef) -> QueryPlanExplanation
```

### 7.6 AOP compilation

Examples:

```text
pc{ execution(* service.*(..)) & attr(transactional) }
```

compiles conceptually to:

```text
SeedTag(aop.join.execution)
Intersect(FilterName(service.*))
Intersect(FilterTag(aop.attr, transactional))
Capture(join_point)
```

`within`, `attr`, `execution`, and `call` become real structural operations rather than partially implemented text checks.

### 7.7 CSS compilation

A CSS selector is compiled into:

- a rightmost-key candidate seed;
- compound-filter operations;
- relationship traversals;
- pseudo-class predicates;
- a stable specificity value;
- invalidation features describing what future DOM changes can affect the selector.

Example:

```css
.panel > button.primary:hover
```

produces:

```text
seed: class(primary) ∩ tag(button)
filter: pseudo(hover)
traverse parent
filter: class(panel)
relationship: direct-child
specificity: (0,3,1)
```

### 7.8 Clang adapter

Simple QueryIR can be:

- evaluated against a flattened canonical Clang AST index; or
- compiled to a supported subset of Clang AST Matchers for direct Clang execution.

The matcher adapter must return canonical `EntityKey` captures, not expose `Decl*`, `Stmt*`, or other Clang pointers beyond the translation-unit lifetime.

---

## 8. MutationIR and transactional transformation

### 8.1 Immutable input, explicit output

Every transformation follows:

```text
Snapshot N
   -> QueryResult
   -> MutationPlan
   -> validate + conflict resolve
   -> execute into new arenas
   -> update mappings + tags + invalidation
   -> verify
   -> commit Snapshot N+1
```

No plugin receives unrestricted mutable access to the authoritative snapshot.

### 8.2 Mutation operation

```simple
struct MutationOp:
    kind: MutationKind
    target: EntityKey
    expected_revision: ArtifactId
    payload: MutationPayloadRef
    precondition: QueryProgramRef?
    origin: MutationOrigin
    priority: i32
    stable_order: u64
    effect: EffectSummary
```

```simple
enum MutationKind:
    AddTag
    RemoveTag
    ReplaceSourceRange
    InsertSourceBefore
    InsertSourceAfter
    ReplaceSyntaxNode
    InsertSyntaxChild
    DeleteSyntaxNode
    ReplaceHirNode
    ReplaceMirInstruction
    InsertMirBefore
    InsertMirAfter
    SplitBasicBlock
    ReplaceLlvmInstruction
    InsertDomChild
    RemoveDomSubtree
    MoveDomSubtree
    SetDomAttribute
    ReplaceDomText
    InsertCssRule
    ReplaceCssRule
    DeleteCssRule
    ReplaceDeclaration
    ReplaceLinkDefinition
    AddRelocation
    ChangePlacementHint
```

### 8.3 Effect summary

```simple
struct EffectSummary:
    reads: EntityKindSet
    writes: EntityKindSet
    creates: EntityKindSet
    deletes: EntityKindSet
    invalidates: DirtyMask
    may_change_control_flow: bool
    may_change_types: bool
    may_change_abi: bool
    may_change_layout_geometry: bool
```

The effect summary is used for conflict detection, pass scheduling, cache invalidation, and verification selection.

### 8.4 Deterministic conflict resolution

Mutations are ordered by:

```text
1. target artifact/entity
2. mutation phase
3. declared priority
4. plugin/advice stable name
5. source order
6. stable operation ordinal
```

Conflict policies:

```simple
enum ConflictPolicy:
    Reject
    HighestPriorityWins
    ComposeIfDisjoint
    RequeryAfterEarlierMutation
    DomainResolver
```

AOP advice ordering uses its established priority semantics but emits a normalized patch sequence. CSS cascade uses a domain resolver based on origin, layer, importance, specificity, and source order. These are different policies operating through the same transaction machinery.

### 8.5 Receipt

```simple
struct MutationReceipt:
    input_snapshot: SnapshotId
    output_snapshot: SnapshotId
    plan_hash: Hash128
    matched_entities: u64
    applied_ops: u64
    skipped_ops: u64
    conflicts: u64
    mapping_delta: MappingShardRef
    tag_delta: TagShardRef
    invalidation: InvalidationSetRef
    verification: VerificationReceipt
```

`plan_hash` read `Hash256` until this ratification and is now **`Hash128`**. The
MutationIR freeze encoded it that way and reported the deviation rather than
silently narrowing it; the narrowing is ratified here, with the reasoning stated
so it is not re-litigated per lane.

Two facts force it. `Hash256` exists in this tree only as a `text` wrapper with
no wire encoding at all, so no lane can encode a 256-bit `plan_hash` today
without first minting a hash width. `Hash128` is already **the** content hash of
the structural wire — frozen by ID-TAG as `hi u64 | lo u64`, 16 bytes, and
already reused by the receipts wave for `MappingShardRef.content_hash` rather
than introducing a second width. Minting a second hash width to serve one field
is the cost side; what is bought is the question.

Nothing is bought here, because of what this field is for. `plan_hash` identifies
a `MutationPlan` for equality and de-duplication **within a snapshot lineage** —
§8.6 `validate`/`apply` compare a plan against a snapshot they already hold. It
is not an external attestation and no adversary chooses its input, so the
relevant bound is birthday collision among plans in one build, and 2^64 is far
past any plan count a build produces. A 256-bit width would buy resistance to a
threat this field is not exposed to.

This is deliberately **not** a general statement that 128 bits replaces 256
across the document. §21.3 keeps `Hash256` for `input_root`, `output_root` and
`deterministic_hash`: those are cross-build reproducibility commitments that get
published and compared between machines, which is exactly the case `plan_hash`
is not. That `Hash256` still has no wire encoding is a real and separate gap,
owned by the receipts lane and tracked as such — it is not repaired by this
ratification. Should `plan_hash` ever become externally attested, widening it is
a v2 field change, not a reinterpretation of the v1 bytes.

### 8.6 Mutation engine API

```simple
interface MutationPlanningPort:
    fn plan(rule: MutationRuleRef, matches: QueryResult) -> MutationPlanRef
    fn merge(plans: [MutationPlanRef], policy: ConflictPolicy) -> MutationPlanRef

interface MutationCommitPort:
    fn validate(plan: MutationPlanRef, snapshot: SnapshotId) -> ValidationReceipt
    fn apply(plan: MutationPlanRef, snapshot: SnapshotId,
             execution: StageExecutionProfile) -> MutationReceipt
    fn publish(receipt: MutationReceipt) -> Result<SnapshotId, CommitError>
```

### 8.7 AOP as MutationIR

AOP becomes a domain frontend:

```text
pointcut syntax
    -> QueryIR
    -> join-point captures
    -> advice-specific MutationIR
    -> MIR/source/runtime adapter
```

Examples:

- `before`: insert advice call before matched operation;
- `after_success`: split or use normal-success exits, then insert call;
- `after_error`: match error edges and insert call;
- `around`: create a continuation/proceed region with an exact-call-count verifier.

The existing requirement that `proceed()` be called exactly once becomes a mutation validator rather than an informal convention.

### 8.8 Optimization point model

Optimization points can be authored or generated:

```simple
@opt_point("serialization.hot_loop")
fn encode(...):
    ...
```

Generated points include:

- loops;
- calls;
- allocations;
- bounds checks;
- branches;
- vectorizable regions;
- GPU-kernel candidates;
- DOM selector hot paths;
- layout islands;
- relocation groups.

Each point receives a stable `EntityKey` and tags such as:

```text
opt.kind
opt.legality
opt.estimated_cost
opt.vector_width
opt.gpu_suitable
profile.hotness
profile.latency_ns
profile.miss_reason
```

### 8.9 Performance mutation loop

```text
instrument candidate points
    -> collect profile artifacts
    -> map profile data back through MappingGraph
    -> QueryIR selects candidates
    -> MutationIR creates variants
    -> semantic/pixel/layout verification
    -> benchmark under identical inputs
    -> publish winning artifact or retain baseline
```

This same loop supports:

- Simple MIR optimization;
- Clang source or LLVM IR optimization;
- CSS selector/index changes;
- DOM representation changes;
- layout-algorithm selection;
- linker grouping and placement changes.

---

## 9. Dependency and invalidation framework

### 9.1 Dirty mask

```simple
flags DirtyMask:
    Source
    Token
    Parse
    SyntaxIndex
    Semantic
    Hir
    Mir
    Optimization
    Codegen
    Link
    DomStructure
    SelectorIndex
    Cascade
    ComputedStyle
    IntrinsicMeasure
    Layout
    Paint
    Composite
    HitTest
    Accessibility
    Resource
```

`DirtyMask` is a **`u32` bitset, and the declaration order above is the wire bit
numbering**: `Source` is bit 0 through `Resource` at bit 20. Twenty-one bits do
not fit a `u16`, so `u32` is the smallest fixed width that holds the frozen set,
leaving bits 21..31 reserved and hard-rejected on the same rule as every other
reserved bit in this document.

The order is load-bearing and not merely conventional. It runs the compiler
pipeline (`Source`..`Link`) and then the document/render pipeline
(`DomStructure`..`Accessibility`), so a stage's bit index is monotone in the
order work actually happens, and `mask < (1 << n)` therefore reads as "nothing
past stage *n* is dirty". Bit positions are wire values: a bit is never reused
and never renumbered, and a new stage takes the next free bit with a version
bump.

**A live divergence is recorded here, with the renumbering that resolves it.**
The layout lane's shorthand constants predate this contract and pack the four
stages that lane cared about into the low bits — `DIRTY_INTRINSIC_MEASURE`,
`DIRTY_LAYOUT`, `DIRTY_HIT_TEST`, `DIRTY_RESOURCE` at 1/2/4/8, i.e. bits 0..3.
Those are **not** the §9.1 positions. The collision is not a near-miss: bit 0
means `IntrinsicMeasure` to the layout lane and `Source` on the wire, so the two
numberings disagree most sharply about the cheapest and the most expensive
invalidation there is.

| Constant | Layout-lane value (bit) | Canonical §9.1 value (bit) |
|---|---|---|
| `DIRTY_INTRINSIC_MEASURE` | 1 (0) | 16384 (14) |
| `DIRTY_LAYOUT` | 2 (1) | 32768 (15) |
| `DIRTY_HIT_TEST` | 4 (2) | 262144 (18) |
| `DIRTY_RESOURCE` | 8 (3) | 1048576 (20) |

The right-hand column is normative; the shorthand constants must be renumbered
onto it.

This is a trap rather than a present defect, and the distinction is worth
recording because it sets how urgently the renumbering must land. It is
currently harmless on three independent counts, each checked rather than
assumed: the layout invalidation contract carries **no encoder** — nothing
serialises those bits, so no divergent bytes exist; every call site consumes the
constants **symbolically**, by name, through `DirtyMask.from_bits` and the
exported identifiers; and a repository-wide search for a numeric dirty literal
reaching `from_bits` or a `dirty_bits` field returns nothing, so no site has
hardcoded a position that renumbering would silently change meaning under.

What makes it a trap is precisely that combination: the two numberings can never
disagree *until* the first byte is written, and at that moment every existing
symbolic call site keeps compiling and keeps passing. The renumbering is
therefore safe to do now and must land **before** anything serialises a
`DirtyMask` — after that point it stops being a rename and becomes a wire break.

### 9.2 Change event

```simple
struct ChangeEvent:
    subject: EntityKey
    kind: ChangeKind
    old_value_hash: Hash128
    new_value_hash: Hash128
    structural_scope: StructuralScope
    source: MutationOrigin
```

### 9.3 Dependency edges

```simple
struct DependencyEdge:
    producer: EntityRef
    consumer: EntityRef
    kind: DependencyKind
    invalidates: DirtyMask
```

Examples:

- exported symbol -> dependent module semantic artifact;
- CSS custom property -> computed declarations that reference it;
- DOM class value -> candidate selector set;
- computed width -> containing block layout;
- font metric -> text fragments and parent intrinsic size;
- input symbol -> relocation and output range.

### 9.4 API

```simple
interface InvalidationPort:
    fn record_dependencies(edges: DependencyEdgeBatch)
    fn derive(change: ChangeBatch, snapshot: SnapshotId) -> InvalidationSetRef
    fn propagate(initial: InvalidationSetRef,
                 budget: InvalidationBudget) -> InvalidationSetRef
    fn explain(entity: EntityRef, dirty: DirtyMask) -> InvalidationTrace
```

### 9.5 Compiler invalidation

Use separate artifact hashes:

```text
content_hash
parse_interface_hash
semantic_interface_hash
implementation_hash
codegen_hash
```

A private implementation change can preserve dependent modules' semantic artifacts while still invalidating code generation and final linking. Macro, AOP, generated-code, and optimization-plugin dependencies are explicit graph edges.

### 9.6 Web invalidation

DOM changes generate feature deltas:

```text
tag changed
id changed
class added/removed
attribute changed
pseudo-state changed
parent changed
sibling order changed
text/empty state changed
subtree inserted/removed
```

CSS selector programs publish invalidation features:

```text
rightmost key
ancestor keys
sibling sensitivity
structural pseudo sensitivity
:has dependency
custom-property reads
media/environment reads
```

The invalidation engine uses these to produce candidate nodes. Computed-style comparison then classifies the actual consequence:

```simple
enum StyleDifference:
    NoChange
    InheritedOnly
    PaintOnly
    CompositeOnly
    IntrinsicMeasure
    LayoutSelf
    LayoutSubtree
    RebuildFormattingContext
```

This replaces the current broad "DOM changed -> rerun everything" behavior while retaining full recomputation as the correctness oracle.

---

# Part II — Extended parser framework

## 10. Parser framework architecture

### 10.1 Components

```text
ParseDialect
    ├─ LexProgram
    ├─ StructureProgram
    ├─ GrammarProgram
    ├─ ActionProgram
    ├─ TagSchema
    ├─ MappingPolicy
    └─ IncrementalPolicy

ParseRuntime
    ├─ scalar CPU executor
    ├─ SIMD executor
    ├─ GPU batch executor
    └─ ordered commit executor
```

### 10.2 Dialect interface

```simple
interface ParseDialect:
    fn dialect_id() -> ParseDialectId
    fn lex_program() -> LexProgramRef
    fn structure_program() -> StructureProgramRef
    fn grammar_program() -> GrammarProgramRef
    fn action_program() -> ActionProgramRef
    fn tag_schema() -> TagSchemaRef
    fn mapping_policy() -> MappingPolicy
    fn incremental_policy() -> IncrementalParsePolicy
```

### 10.3 Request and result

```simple
struct ParseRequest:
    source: ArtifactRef
    prior_snapshot: SnapshotId?
    edits: ObjectRef<TextEditArena>?
    entry_rule: GrammarRuleId
    outputs: ParseOutputMask
    tag_demand: TagDemand
    execution: StageExecutionProfile
    placement: PlacementPolicyRef

struct ParseResult:
    source: ObjectRef<SourceBlob>
    tokens: ObjectRef<TokenArena>
    structure: ObjectRef<StructureArena>
    syntax: ObjectRef<SyntaxArena>
    tags: TagShardRef
    mappings: MappingShardRef
    indexes: QueryIndexShardRef
    diagnostics: ObjectRef<DiagnosticArena>
    invalidation: InvalidationSetRef
    receipt: StageReceipt
```

### 10.4 Semantic-action sink

```simple
interface ParseActionSink:
    fn reserve_nodes(count: u32) -> NodeRange
    fn emit_node(kind: NodeKindId, span: SourceSpan,
                 children: EntityRange) -> EntityRef
    fn emit_tag(node: EntityRef, key: TagKeyId, value: TagValue)
    fn emit_mapping(source: SourceAnchor, node: EntityRef, kind: MappingKind)
    fn emit_index(key: QueryIndexKey, node: EntityRef)
    fn emit_diagnostic(diag: DiagnosticRecord)
```

A grammar action can emit tags and mappings in the same deterministic count/scan/emit pass used for nodes. No callback allocates arbitrary host objects.

### 10.5 Lexical GPU execution

For each chunk, calculate:

```text
Fchunk(entry_lex_state) -> exit_lex_state
```

Compose chunk functions with a scan, then emit tokens using exact precomputed offsets:

```text
classify -> summarize -> scan states -> count -> scan offsets -> emit
```

This applies to:

- Simple strings/comments/indentation;
- CSS comments/strings/URLs/escapes;
- HTML tokenizer states;
- preprocessed C/C++ tokens or constrained raw-source scanning.

### 10.6 Structural-first SIMD path

The hybrid CPU mode uses SIMD for:

- UTF validation;
- delimiter and quote classification;
- newline and indentation discovery;
- candidate identifier and number boundaries;
- HTML `<`, `>`, `&`, quote, and comment markers;
- CSS brace, colon, semicolon, string, and comment markers.

The scalar parser consumes structural indexes rather than re-reading every byte through branch-heavy code.

### 10.7 Region parsing

The framework identifies independently parseable regions:

- Simple top-level declarations and function bodies;
- CSS rule/declaration blocks;
- static HTML subtrees after ordered boundary discovery;
- preprocessed C function bodies for experimental constrained parsing.

Each region records entry state, grammar rule, token range, parent region, and expected output size. Large regions execute one warp/workgroup each; small regions are packed.

### 10.8 Incremental parsing

Incremental parsing operates on immutable revisions:

1. map edits to byte ranges;
2. expand to lexical stabilization boundaries;
3. re-tokenize affected chunks;
4. re-establish delimiter/indentation summaries;
5. identify changed parse regions;
6. reuse unchanged syntax arenas by artifact reference;
7. emit mapping edges from retained old entities to new entities;
8. invalidate dependent semantic/style/layout stages.

### 10.9 Supported dialect profiles

| Dialect | Initial CPU path | Initial hybrid path | Initial resident-GPU path |
|---|---|---|---|
| Simple | canonical parser | SIMD/GPU lex + structure; CPU region parser | GPU lex/structure/eligible region parser |
| CSS | syntax-token parser | SIMD/GPU token, selector/declaration batches | rules/selectors/indexes resident GPU |
| HTML | ordered tokenizer/tree builder | GPU tokenizer + CPU ordered tree commit | resident token/DOM arenas; CPU ordered/script commit |
| Clang C/C++ | Clang authoritative frontend | GPU prefilter/index/export around Clang | Clang semantics + resident canonical AST/IR indexes |
| constrained preprocessed C | optional parser | GPU region parser | experimental almost-full GPU frontend |

---

# Part III — Simple compiler integration

## 11. Canonical compiler sidecars

Do not widen every existing AST/HIR/MIR entity. Add sidecar artifacts:

```text
AstArena
AstTagShard
AstOriginShard
AstQueryIndexShard

HirArena
HirTagShard
HirOriginShard

MirArena
MirTagShard
MirOriginShard
MirProfileShard
```

Each MDSOC transform maps both the primary entity view and demanded sidecars.

### 11.1 Extended feature ports

```simple
struct ParsingOutputPort:
    ast: AstView
    tags: TagShardRef
    origins: MappingShardRef
    indexes: QueryIndexShardRef
    diagnostics: DiagnosticArenaRef

struct OptimizationInputPort:
    mir: MirOptView
    tags: TagShardRef
    origins: MappingShardRef
    profile: ProfileArtifactRef?
    query_indexes: QueryIndexShardRef

struct OptimizationOutputPort:
    mir: MirOptView
    tags: TagShardRef
    origins: MappingShardRef
    mutation: MutationReceipt
    remarks: OptimizationRemarkArenaRef

struct LinkingInputPort:
    objects: [ObjectFileView]
    tags: TagShardRef
    origins: MappingShardRef
    placement_hints: PlacementHintShardRef
```

### 11.2 Required transform additions

Every existing boundary receives a sidecar mapper:

```text
lexing_to_parsing       source/token tags -> syntax tags
parsing_to_desugaring   preserve or replace syntax origins
typing_to_hir           resolved symbol/type tags -> HIR tags
hir_to_mir              control/data-flow tags -> MIR tags
mir_to_optimizer        optimization points/profile keys
mir_to_backend          code/object origins
backend_to_linker       symbol/section/output mappings
```

### 11.3 AOP upgrade plan

1. Compile `pc{...}` into QueryIR.
2. Replace duplicated text matchers with one QueryIR evaluator and thin legacy adapters.
3. Fully implement `attr`, `within`, `execution`, and `call` through tags and indexes.
4. Add assignment, decision, condition, and error selectors over syntax/MIR tags.
5. Represent advice as MutationIR templates.
6. Emit exact provenance from advice call/instruction to advice declaration and original join point.
7. Verify around-advice control flow and `proceed()` cardinality.
8. Preserve zero allocation and zero weaving work when no AOP rules are enabled.

### 11.4 Optimizer upgrade plan

1. Preserve the existing optimizer manifest and pass registry.
2. Replace line-pattern source matching with QueryIR.
3. Extend pass contracts:

```simple
struct OptimizationPassContract:
    input_schema: EntitySchemaId
    output_schema: EntitySchemaId
    required_tags: TagKeySet
    produced_tags: TagKeySet
    required_indexes: TagIndexSet
    mutation_kinds: MutationKindSet
    effect: EffectSummary
    legality_verifier: VerifierId
    backend_policy: BackendPolicy
    cost_model: CostModelId
```

4. Route source, MIR, and profile-driven passes through the same query/mutation engine.
5. Store optimization remarks as structured tags and receipts.
6. Map hotness and missed optimization reasons back to source entities through MappingGraph.

### 11.5 Simple compiler modes

| Stage | `cpu_reference` | `hybrid_vector_gpu` | `resident_gpu` |
|---|---|---|---|
| file/hash/cache | ordinary host I/O | SIMD hash + batched GPU hash | SSD/direct-to-GPU artifact batches |
| lex/structure | current canonical CPU | SIMD/GPU classification and scans | resident GPU token/structure arenas |
| parse | CPU canonical parser | CPU region parser over accelerated tokens | eligible region parsers on GPU; CPU fallback |
| semantic/type | CPU | GPU indexes/bulk probes; CPU decisions | resident tables and eligible graph passes; CPU irregular fallback |
| HIR/MIR | CPU | bulk transforms/analyses on GPU | resident SoA transforms where implemented |
| optimize | current CPU pass manager | cost-selected GPU analyses/mutations | resident QueryIR/MutationIR passes |
| codegen | current backends | selected GPU code/object preparation | resident device-target pipelines where supported |
| link | current SMF/native path | GPU symbol/layout/relocation batches | resident SMF linker and direct/staged output |

The CPU mode remains the oracle and is never deleted.

---

# Part IV — Clang and LLVM bridge

## 12. Clang bridge architecture

The production bridge should initially **wrap and extend Clang**, not replace its full language frontend.

```text
CompilationDatabase
   -> Clang FrontendAction
      -> PP callbacks + ASTConsumer
         -> canonical flat AST export
         -> tags/origins/query indexes
         -> source MutationIR adapter
   -> LLVM PassBuilder plugin
      -> IR tags/origins/query indexes
      -> IR MutationIR adapter
      -> optimization remarks/profile mapping
```

### 12.1 Components

```text
simple-clang-export
    FrontendAction, PPCallbacks, ASTConsumer, SourceManager mapping

simple-clang-query
    QueryIR <-> AST Matcher adapter

simple-clang-transform
    MutationIR <-> clang::transformer/Replacements adapter

simple-llvm-pass
    PassBuilder plugin, pass instrumentation, metadata, MutationIR

simple-clang-profile
    optimization remarks, PGO/sample profile, hotness mapping
```

### 12.2 Clang entity identity

Raw Clang pointers are translation-unit-local and non-persistent. Export:

```simple
struct ClangEntityIdentity:
    tu_artifact: ArtifactId
    ast_kind: u32
    source: SourceAnchor
    semantic_usr: StringId?
    local_ordinal: u32
```

- declarations prefer a USR/signature semantic key plus source anchor;
- statements and expressions use source anchor, kind, parent identity, and deterministic ordinal;
- macro entities preserve spelling and expansion locations;
- generated/implicit declarations are tagged and receive synthetic origins.

### 12.3 Clang AOP

Pointcut dialect examples:

```text
execution(function(name("service.*")) & attr("transactional"))
call(callee(type("Database")))
within(namespace("api")) & branch(profile.hotness > threshold)
```

Execution options:

- compile to AST Matcher where the construct has a direct matcher;
- otherwise query the canonical exported AST;
- lower source-safe weaving to Clang Replacements;
- lower control-flow-sensitive weaving to LLVM IR MutationIR;
- reject or require explicit policy for rewrites inside macro definitions, system headers, generated files, or templates with ambiguous instantiations.

### 12.4 Clang performance mutation

The framework combines:

- AST tags and captures;
- LLVM IR tags and mappings;
- pass instrumentation events;
- optimization remarks;
- profile counts and hotness;
- binary/linker mappings.

Example loop:

```text
remark: loop not vectorized
    -> map LLVM loop to Clang source loop
    -> tag opt.missed_reason and profile.hotness
    -> query loops meeting policy
    -> source or IR mutation candidate
    -> compile variant
    -> test + benchmark
    -> accept/reject receipt
```

### 12.5 Clang three-mode plan

#### Mode C0 — `cpu_reference`

- normal Clang preprocessor, parser, Sema, AST, code generation, LLVM passes, and linker;
- Simple framework runs CPU queries, tags, source rewrites, and receipts;
- no GPU dependency;
- authoritative correctness and diagnostics path.

#### Mode C1 — `hybrid_vector_gpu`

CPU remains authoritative for preprocessing, C++ parsing, templates, Sema, and diagnostics. Offload:

- source hashing and compilation-database batching;
- SIMD token/structural pre-indexing;
- include/macro candidate indexing where safe;
- flattened AST transfer and bulk QueryIR evaluation;
- AOP match grouping and safe rewrite-template expansion;
- selected LLVM graph/data-flow analyses;
- profile/remark aggregation;
- linker hash/sort/reachability/relocation stages.

#### Mode C2 — `resident_gpu`

- canonical source/token/flat-AST/tag/query/LLVM-IR sidecars remain in Object VM;
- bulk AOP and optimizer queries execute without host readback;
- safe mutation templates and eligible LLVM transforms run on GPU;
- device objects and link inputs remain resident;
- host receives compact receipts and diagnostics only.

Clang still performs unsupported preprocessor/Sema/template operations and serves as the oracle. A genuinely all-GPU C/C++ frontend is a separate experimental project. The realistic first "almost all" target is preprocessed C or a constrained C++ profile.

### 12.6 Version and compatibility policy

```simple
struct ClangAdapterCapability:
    clang_major: u16
    ast_export_schema: u16
    matcher_adapter_version: u16
    transformer_adapter_version: u16
    llvm_ir_schema: u16
    supported_features: ClangFeatureSet
```

Build and test one adapter per supported Clang major. Reject unknown majors rather than silently assuming ABI compatibility.

`supported_features` was declared `CapabilitySet`, a type this document never
defined. It is ratified as **`ClangFeatureSet`, a `u32` bitset with one bit per
component that §12.1 enumerates**, and the field is renamed accordingly above.
Both halves of that — the rename and the vocabulary — were forced, not chosen.

The rename is forced because `CapabilitySet` is not an undefined name, it is a
*taken* one: it is a live kernel type (`src/os/kernel/types/capability_types.spl`)
carrying capability tokens and pledge state, used at over a hundred sites across
the kernel's IPC, session and container code. A Clang adapter feature bitset and
a kernel capability set share nothing but the word "capability". Keeping the
collision would mean the one name resolves to two unrelated types depending on
which lane imports it, which is the same-name-different-meaning failure the
freeze rules exist to prevent.

The vocabulary is forced because §12.1 already enumerates the members — this
ratification does not invent a feature list, it reads the one this chapter
states. §12.1 names exactly five components, and `ClangFeatureSet` defines
exactly one bit per component, in §12.1's order: `simple-clang-export`,
`simple-clang-query`, `simple-clang-transform`, `simple-llvm-pass`,
`simple-clang-profile`, at bits 0..4. Each bit asserts that this adapter build
ships that component — nothing broader, so the set cannot drift into a general
capability vocabulary that §12.1 does not back.

Bits 5..31 are reserved and must be zero, hard-rejected like every other
reserved bit here. The consequence is specific enough to state: a reader that
masked an unknown bit off would conclude an adapter *lacks* a capability it is
advertising, and would then select a fallback path with no reason to record for
it — the unexplained degradation §21.4 forbids.

---

# Part V — HTML, CSS, DOM, and renderer

## 13. Canonical web data model

### 13.1 DOM SoA

Replace the long-term object-heavy representation with canonical arenas:

```simple
struct DomArena:
    kind: [DomNodeKind]
    parent: [i32]
    first_child: [i32]
    next_sibling: [i32]
    tag_name: [StringId]
    text_span: [SourceSpan]
    attr_start: [u32]
    attr_count: [u16]
    flags: [u32]

struct DomAttributeArena:
    owner: [u32]
    name: [StringId]
    value: [StringId]
    namespace: [StringId]
```

`NodeId` is a document-local `EntityRef`. Node IDs remain stable inside one committed snapshot. A new navigation creates a new artifact and invalidates old IDs.

### 13.2 CSS rule IR

```simple
struct CssRuleArena:
    kind: [CssRuleKind]
    selector_program: [QueryProgramRef]
    declaration_start: [u32]
    declaration_count: [u16]
    origin: [CssOrigin]
    layer: [u32]
    source_order: [u32]
    condition: [CssConditionRef]

struct CssDeclarationArena:
    property: [CssPropertyId]
    value_program: [CssValueProgramRef]
    important: [bool]
    source: [SourceAnchor]
```

### 13.3 Computed style sharing

Do not keep one giant independently allocated mutable `Style` object per node. Use:

```simple
struct ComputedStyleTable:
    records: ObjectRef<StyleRecordArena>
    node_style_id: [StyleId]
    inherited_fingerprint: [Hash64]
    layout_fingerprint: [Hash64]
    paint_fingerprint: [Hash64]
    composite_fingerprint: [Hash64]
```

Identical immutable style records are hash-consed. Frequently accessed layout properties may be decoded into compact hot columns for the layout pass.

---

## 14. HTML parser with tagging and mutation

### 14.1 Browser-compatible profile

```text
GPU/SIMD tokenizer
    -> token arena + source mappings + tag/attribute indexes
    -> ordered tree-builder commit
    -> immutable DOM snapshot
```

The ordered commit owns:

- insertion mode;
- open-element stack;
- active formatting elements;
- foster parenting and error recovery;
- script/parser interaction;
- document write or equivalent input mutation policy.

### 14.2 Static-template profile

For trusted Simple UI templates or documents with no parser-blocking script mutation:

- identify balanced structural regions;
- construct independent subtrees in parallel;
- merge through deterministic parent slots;
- run full ordered parser as a verification oracle until parity is proven.

### 14.3 HTML tags and mappings

Parser tags include:

```text
dom.kind
dom.tag_name
dom.id
dom.class
dom.attr_name
dom.has_text
dom.is_form_control
dom.is_link
dom.is_style_element
dom.is_script_element
dom.parser_inserted
dom.error_recovered
```

Mappings include:

```text
HTML source range -> token
HTML token -> DOM node
attribute source range -> DOM attribute
DOM node -> generated pseudo/layout entities
```

### 14.4 DOM mutation transaction

```simple
struct DomMutationBatch:
    document: SnapshotId
    operations: ObjectRef<DomMutationArena>
    script_origin: ScriptOrigin?
    event_epoch: u64

interface DomMutationPort:
    fn validate(batch: DomMutationBatch) -> DomValidationReceipt
    fn apply(batch: DomMutationBatch,
             execution: StageExecutionProfile) -> MutationReceipt
```

Script and event code append commands to a bounded mutation buffer. Commit occurs at defined event-loop checkpoints, producing one new DOM snapshot and one invalidation batch.

---

## 15. CSS parser, CSS mutation, and style linking

### 15.1 CSS parser stages

```text
UTF/token classification
    -> component-value parsing
    -> block/function pairing
    -> selector compilation to QueryIR
    -> declaration/value bytecode
    -> invalidation-feature extraction
    -> rule/property/resource indexes
```

### 15.2 CSS mutation classes

```simple
enum CssChangeKind:
    AddRule
    DeleteRule
    ReplaceSelector
    ReplaceDeclaration
    ChangeRuleOrder
    ChangeLayerOrder
    ChangeMediaCondition
    ChangeCustomProperty
    ChangeKeyframes
    ChangeFontFace
```

### 15.3 Exact invalidation strategy

- declaration-only change with unchanged selector:
  - reuse current match set;
  - recompute only affected properties for matched nodes;
- selector change:
  - remove old selector's candidate/match contribution;
  - query candidates using new selector feature indexes;
- class/ID/attribute DOM change:
  - query only selectors whose invalidation features mention the changed key;
- structural mutation:
  - include selectors sensitive to descendant, child, sibling, `:empty`, `:nth-*`, or `:has` relations;
- custom-property change:
  - traverse property dependency graph;
- media/viewport change:
  - activate/deactivate affected rule groups, then style-diff matched nodes.

### 15.4 StyleLinker

A web document needs a resolver distinct from binary linking:

```text
stylesheet URL/import graph
custom-property definitions/references
font-face definitions/uses
keyframe definitions/uses
image/resource URLs
component/template definitions
```

`WebResourceLinkProfile` specializes the shared resolve framework and emits:

```simple
struct StyleLinkResult:
    resolved_rules: CssRuleArenaRef
    custom_property_graph: DependencyGraphRef
    resource_bindings: ResourceBindingArenaRef
    definition_mappings: MappingShardRef
    diagnostics: DiagnosticArenaRef
```

---

## 16. Style calculation modes

### 16.1 `cpu_reference`

- current canonical HTML/CSS/DOM semantics;
- scalar or ordinary CPU selector matching and cascade;
- full recomputation available as oracle;
- deterministic tree/order behavior.

### 16.2 `hybrid_vector_gpu`

CPU owns HTML tree commit, script, event ordering, and difficult selectors. SIMD/GPU handles:

- CSS tokenization and selector compilation;
- candidate generation by ID/class/tag/attribute bitsets;
- bulk compound-selector filtering;
- matched declaration collection;
- stable cascade key sorting/group reduction;
- shared computed-style hashing;
- style-difference classification.

### 16.3 `resident_gpu`

- DOM, attributes, rule IR, selector indexes, match sets, and computed styles remain resident;
- script/event CPU sends bounded DOM mutation command buffers;
- GPU applies validated bulk patches, updates indexes, matches selectors, and computes style deltas;
- CPU handles unsupported selectors, ordered script-visible results, security, and compact commit receipts.

---

# Part VI — HTML spatial layout manager

## 17. Spatial layout architecture

### 17.1 Input and output

```simple
struct LayoutInputSnapshot:
    dom: DomSnapshotRef
    styles: ComputedStyleSnapshotRef
    viewport: ViewportState
    fonts: FontMetricSnapshotRef
    resources: ResourceMetricSnapshotRef
    prior_layout: LayoutSnapshotRef?
    invalidation: InvalidationSetRef

struct LayoutSnapshot:
    fragments: LayoutFragmentArenaRef
    boxes: LayoutBoxArenaRef
    hit_index: HitIndexRef
    dependencies: DependencyGraphRef
    mappings: MappingShardRef
    receipt: StageReceipt
```

### 17.2 Layout islands

The layout planner partitions the document by formatting-context and containment boundaries:

```simple
struct LayoutIsland:
    root: EntityRef
    profile: LayoutProfileId
    dependency_start: u32
    dependency_count: u16
    estimated_work: u32
    input_fingerprint: Hash128
    dirty: DirtyMask
```

Typical island boundaries:

- block formatting context;
- flex container;
- grid container;
- table formatting context;
- independent absolute-position context;
- layout containment boundary;
- scroll container;
- isolated iframe/document.

Inline formatting may be a subgraph because line breaking and text shaping have sequential dependencies within each paragraph.

### 17.3 Layout profiles

```simple
interface SpatialLayoutProfile:
    fn profile_id() -> LayoutProfileId
    fn discover_islands(input: LayoutInputSnapshot) -> LayoutIslandArenaRef
    fn estimate(island: LayoutIsland, mode: ExecutionMode) -> CostEstimate
    fn measure(islands: LayoutIslandSet, ctx: LayoutContext) -> MeasureResult
    fn arrange(islands: LayoutIslandSet, ctx: LayoutContext) -> LayoutFragmentArenaRef
    fn verify(result: LayoutFragmentArenaRef, oracle: LayoutSnapshotRef?) -> VerificationReceipt
```

Initial profiles:

```text
block
inline
flex
grid
table
absolute/sticky
scroll
replaced elements/images
```

### 17.4 Dependency scheduling

Layout is not a single top-down pass. The scheduler uses:

- intrinsic-size dependencies;
- containing-block dependencies;
- percentage resolution;
- min/max constraints;
- baseline groups;
- grid track dependencies;
- table column/row constraints;
- font and resource metrics.

The planner creates a directed graph, condenses strongly connected components, and runs topological waves. Cyclic or fixed-point contexts use bounded iteration with a CPU oracle/fallback.

### 17.5 Layout mutation and invalidation

DOM/style changes mark only affected islands. Examples:

- color change: no layout work;
- width/padding/font-size change: node and containing context dirty;
- child insertion: parent formatting context and downstream siblings dirty;
- absolute-position-only change: positioned subtree dirty, normal flow retained;
- font metric change: text runs, line boxes, intrinsic ancestors dirty;
- viewport media change: styles first, then layout islands whose geometry fingerprint changed.

### 17.6 Layout modes

| Mode | Execution |
|---|---|
| `cpu_reference` | current/authoritative algorithms; deterministic full and incremental paths |
| `hybrid_vector_gpu` | per-island cost model; large homogeneous flex/grid/block batches on GPU; CPU text shaping and small/irregular contexts |
| `resident_gpu` | DOM/style/layout arrays resident; supported islands execute GPU measure/arrange; CPU returns only fallback fragment deltas |

### 17.7 Text shaping boundary

Text shaping is a separate port:

```simple
interface TextMeasurePort:
    fn shape(requests: TextShapeRequestArenaRef,
             execution: StageExecutionProfile) -> TextShapeResultArenaRef
```

Do not approximate complex-script shaping merely to keep layout on GPU. GPU layout may consume CPU-produced glyph metrics until a verified GPU text backend exists.

---

# Part VII — Resolve framework and linkers

## 18. Generic GraphResolveCore

### 18.1 Shared concepts

```simple
struct DefinitionRecord:
    key: ResolveKey
    owner: EntityRef
    attributes: ResolveAttributeSet
    order: StableOrderKey

struct ReferenceRecord:
    key: ResolveKey
    owner: EntityRef
    attributes: ResolveAttributeSet
    order: StableOrderKey

struct ResolutionRecord:
    reference: EntityRef
    definition: EntityRef?
    status: ResolutionStatus
    reason: ResolutionReason
```

```simple
interface ResolveProfile:
    fn collect(snapshot: SnapshotId) -> ResolveInputRef
    fn group_key(record: ResolveRecord) -> ResolveKey
    fn resolve_group(group: ResolveGroupView) -> ResolveGroupResult
    fn derive_constraints(result: ResolveGroupResult) -> ConstraintBatch
    fn plan_placement(result: ResolveResultRef) -> DomainPlacementRef
    fn emit(result: ResolveResultRef) -> MutationPlanRef
```

The core provides:

- hash/intern;
- stable sort/group;
- deterministic group reduction;
- reachability frontiers;
- constraint propagation;
- scan-based placement;
- patch emission;
- receipts and diagnostics.

### 18.2 Profiles

```text
SmfLinkProfile
    symbols, sections, relocations, output addresses

ClangOffloadLinkProfile
    host/device images, target triples, embedded offload sections,
    runtime registration records

WebResourceLinkProfile
    stylesheet imports, URLs, fonts, keyframes, custom properties,
    script/module/component resources
```

Spatial HTML layout is **not** a ResolveProfile. It uses resolution outputs but has its own geometry semantics.

---

## 19. Simple SMF linker

### 19.1 Pipeline

```text
L0  discover inputs and stable input order
L1  decode/validate SMF tables
L2  create symbol/section/relocation arenas and tags
L3  intern names and stable-sort symbol groups
L4  deterministic definition selection and diagnostics
L5  archive/module extraction fixed point
L6  reachability/dead stripping
L7  section grouping and scan-based address layout
L8  relocation grouping and application
L9  output chunk assembly
L10 provenance map: input entities -> output byte ranges
L11 staged/direct SSD write
L12 host receipt verification and manifest commit
```

### 19.2 Linker tags and optimization points

```text
link.symbol.binding
link.symbol.visibility
link.symbol.resolution
link.section.kind
link.section.alignment
link.relocation.kind
link.reachable
link.icf.candidate
link.hot_order
link.output_range
```

The linker may receive profile tags for function/section ordering. Any layout mutation emits a new address mapping and invalidates affected relocations and debug/source maps.

### 19.3 Linker modes

| Mode | Behavior |
|---|---|
| `cpu_reference` | current SMF reader/writer/linker, upgraded to canonical arenas and receipts |
| `hybrid_vector_gpu` | CPU decode/control; GPU hash, sort, resolve, reachability, scans, relocation batches |
| `resident_gpu` | objects/symbols/relocations/output chunks remain in Object VM; compact host commit only |

Native ELF/Mach-O/PE remains delegated to established native linkers until a measured need justifies format-specific GPU profiles.

---

# Part VIII — GPU Object VM and residency placement

## 20. Residency tiers

```simple
enum ResidencyTier:
    DeviceLocal
    DeviceShared
    HostPinned
    HostHot
    HostCold
    SsdCas
    Recomputable
```

`Recomputable` means no stored copy is required because the object can be regenerated from recorded immutable inputs and transform identity.

### 20.1 Object granularity

Object VM manages arenas/chunks such as:

- source blob or source chunk;
- token arena;
- AST column group;
- tag/mapping shard;
- string-interner shard;
- HIR/MIR function group;
- DOM subtree shard;
- CSS rule shard;
- computed-style table;
- layout-island batch;
- SMF section/relocation shard;
- output chunk.

It does not manage each node separately.

### 20.2 Placement request

```simple
struct PlacementRequest:
    object: ObjectRef<AnyObject>
    access: AccessPattern
    required_tiers: ResidencyTierSet
    preferred_tiers: [ResidencyTier]
    device_mask: DeviceMask
    expected_first_use: StageEpoch
    expected_last_use: StageEpoch
    expected_reuse_distance: u32
    recompute_cost: CostUnit
    transfer_cost_hint: CostUnit
    persistence: PersistencePolicy
    affinity_group: AffinityGroupId
    deadline: Deadline?
```

### 20.3 Placement plan

```simple
struct PlacementPlan:
    reservations: ObjectRef<ReservationArena>
    transfers: ObjectRef<TransferArena>
    evictions: ObjectRef<EvictionArena>
    prefetches: ObjectRef<PrefetchArena>
    leases: ObjectRef<LeaseArena>
    estimated_cost: CostEstimate
    receipt_seed: Hash256
```

### 20.4 Backend interface

```simple
interface PlacementBackend:
    fn probe() -> PlacementCapabilities
    fn plan(requests: PlacementRequestArenaRef,
            budget: PlacementBudget) -> PlacementPlan
    fn acquire(plan: PlacementPlan) -> Result<LeaseSet, PlacementError>
    fn prefetch(plan: PlacementPlan) -> Result<TransferReceipt, PlacementError>
    fn checkpoint(objects: ObjectSetView) -> CheckpointReceipt
    fn release(leases: LeaseSet)
    fn recover(root: ArtifactId) -> RecoveryReceipt
```

### 20.5 Lease-bound resident view

```simple
struct ResidentView<T>:
    device_address: u64
    length: u64
    object_slot: u32
    lease_epoch: u32
```

A raw address may be used only inside the lease epoch. Persistent artifacts, queues, tags, mappings, and cross-stage references store object/entity IDs, not addresses.

### 20.6 Placement planner

The planner combines:

- compile-time stage DAG and liveness intervals;
- Object VM state;
- measured transfer bandwidth and latency;
- recomputation cost;
- next-use estimate;
- affinity groups;
- host/VRAM/SSD budgets;
- dirty/checkpoint status;
- pin/in-flight status.

Suggested score:

```text
retain_score =
    expected_reuse_probability
    * min(reload_cost, recompute_cost)
    / resident_bytes
```

This is only one heuristic; policy remains pluggable and is verified against fixed workloads.

### 20.7 Storage backends

```text
staged
    SSD -> bounded pinned host ring -> VRAM
    mandatory portable backend

direct
    SSD -> VRAM using supported direct-storage facility
    optional capability

device_initiated
    GPU-managed request queues/cache/NVMe interaction
    experimental capability
```

### 20.8 Host-memory bound

The production acceptance condition is:

```text
peak_host_RSS <=
    fixed_runtime_base
    + configured_staging_budget
    + bounded_driver_and_queue_budget
    + bounded_manifest/index_cache
```

It must not scale linearly with total source bytes, AST nodes, DOM nodes, object files, or linked output size.

### 20.9 Metadata overhead target

- one 32–48 byte hot descriptor per object arena/chunk;
- entity references use compact indexes already needed by the IR;
- tag and mapping shards are compressed and demand-driven;
- cold hashes, paths, and dependency metadata reside in SSD-side manifests;
- no descriptor per syntax/DOM/layout node.

---

# Part IX — Unified execution framework

## 21. Execution profile

```simple
enum ExecutionMode:
    CpuReference
    HybridVectorGpu
    ResidentGpu

struct StageExecutionProfile:
    mode: ExecutionMode
    deterministic: bool
    host_memory_budget: u64
    device_memory_budget: u64
    latency_target_us: u64
    throughput_target: u64
    fallback: FallbackPolicy
    verification: VerificationPolicy
    allowed_devices: DeviceMask
```

This record was written `ExecutionProfile` and is renamed **`StageExecutionProfile`**
here, matching the name the EXEC freeze gave it on the wire. The rename is
ratified into the architecture so the document and the frozen encoder agree; the
frozen name is not changed to match the document, because the document's name was
the one that was already taken.

`ExecutionProfile` names a different and unrelated record in this tree
(`common/structural/execution/contracts.spl`): it carries `cpu_us`,
`gpu_kernel_us`, `scheduling_us`, `transfer_us_per_kib` and `sync_us` — that is
**measured cost, after the fact**. The §21 record carries determinism, budgets,
targets and policies — **what was requested, before the fact**. They share no
field but `mode`. The two are not merely different, they are the two halves of
the no-silent-fallback guarantee: §21.3's receipt records what a stage actually
did, and this record records what it was permitted to do, so comparing them is
how a forced degradation is told apart from a cost-policy CPU choice. Collapsing
them onto one name would erase exactly that distinction.

`Stage` is the right qualifier rather than an arbitrary disambiguator: §21.1's
`estimate(request, profile)` is a per-stage call, and the frozen `Stage*` family
already contains `StageReceipt` and `StageFallbackReason`.

The measured-cost record keeps its name for now. Freeing the bare
`ExecutionProfile` would mean renaming it to `ExecutionCostProfile` across the
modules that read it — a real mechanical change, not a cosmetic one — and it
buys a name that nothing needs any more, since §21's record is now distinctly
named at both the document and the wire. That rename is therefore recorded as
**tracked and optional, not blocking**: no consumer lane is waiting on it, and it
touches no wire layout, because the measured-cost record has no encoder.

One consumer is already mis-pointed by exactly this collision, and it is the
reason the collision is worth ratifying rather than tolerating. The compiler's
per-stage offload profile declares a field as "budgets/devices from the EXEC
owner" and types it `ExecutionProfile` — but the record it names has no budget
field and no device field, so the comment describes `StageExecutionProfile` while
the type resolves to the measured-cost record. The field is meant to carry what
the stage was *permitted* to use, so it must be re-pointed at
`StageExecutionProfile`; its constructors change with it. That is a code change,
specified and reported here, not made by this ratification.

The failure mode this illustrates is the general one: the collision does not
produce a compile error, it produces a field that type-checks, carries plausible
zeros, and silently answers "what was this stage allowed to do?" with a record
that cannot express the question.

```simple
interface StageBackend<Request, Result>:
    fn capabilities() -> StageCapabilities
    fn estimate(request: Request,
                profile: StageExecutionProfile) -> CostEstimate
    fn plan(request: Request,
            profile: StageExecutionProfile,
            placement: PlacementSnapshot) -> StagePlan
    fn execute(plan: StagePlan) -> Result
    fn verify(result: Result,
              policy: VerificationPolicy) -> VerificationReceipt
```

### 21.2 Cost estimate

```simple
struct CostEstimate:
    cpu_work: u64
    simd_work: u64
    gpu_work: u64
    host_to_device_bytes: u64
    device_to_host_bytes: u64
    ssd_read_bytes: u64
    ssd_write_bytes: u64
    synchronization_points: u32
    predicted_latency_us: u64
    confidence_milli: u16
```

The scheduler chooses GPU only when expected total cost, including transfer and synchronization, beats the CPU path under the requested latency/throughput objective.

**This is the one and only `CostEstimate` in this document, and its byte layout
is frozen.** Fields in the order above, little-endian, no padding: seven `u64`
work and byte counters (56 B), `synchronization_points` `u32` (4 B),
`predicted_latency_us` `u64` (8 B), `confidence_milli` `u16` (2 B) — **70 bytes**.

That layout is not negotiable per lane, because §20.3 embeds `CostEstimate`
**by value** in `PlacementPlan`. An embedded record has no indirection to hide a
disagreement behind: if the EXEC lane's `estimate` returned a differently-shaped
`CostEstimate`, a `PlacementPlan` produced by PLACE and a cost produced by a
stage backend would be two different records wearing one name, and the
embedding is what makes that undetectable rather than a type error. **EXEC must
adopt this exact 70-byte layout**; the freeze that PLACE performed is normative
for both.

Both `estimate` signatures in this document return this record — §21.1's
`StageBackend.estimate` and §17.3's `SpatialLayoutProfile.estimate`. §17.3 was
never given a second definition and does not get one.

A divergence exists in the tree and is recorded here rather than left to be
rediscovered by each of the consumer lanes. The structural-layout contract
declares its own `CostEstimate` — `island_root_id`, `estimated_work`, `cpu_us`,
`gpu_kernel_us`, `scheduling_us`, `host_to_device_bytes`, `device_to_host_bytes`,
`synchronization_points`, `predicted_gpu_us`, all `i64`. It shares only
`synchronization_points` and the two transfer-byte fields with the record above,
and it is a *different kind* of quantity: it is per-island and denominated in
elapsed microseconds already attributed to a stage, where §21.2 is per-request
and denominated in abstract work plus a predicted latency. It is a genuine and
useful record; it is simply not this one. It must be renamed — `LayoutIslandCost`
is the accurate name — so that §17.3's `estimate` can return the §21.2 record it
is declared to return. That is a code change, tracked and reported, not made by
this ratification.

One further declaration of the name exists, in the MIR auto-vectorisation cost
model. It is unrelated to §20/§21 entirely — it costs loop vectorisation
decisions inside the optimiser and never crosses a structural-compute boundary —
so it is out of scope here and needs no rename beyond noting that a repository
search for `CostEstimate` returns three declarations, not two.

`CostEstimate` must stay converged with the compiler's collection cost algebra
(`CostExpr`/`MemoryExpr`/`CardinalityExpr` and the REG1 operation-cost registry
`config/compiler/collection_operations.sdn` — see
`doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
§4–§5). Two independently maintained op-cost tables will diverge; when a
QueryIR dialect needs a per-op cost, source it from that registry and extend
the registry rather than hardcoding a second table here.

### 21.3 Stage receipt

```simple
struct StageReceipt:
    stage: StageId
    backend: BackendId
    mode: ExecutionMode
    input_root: Hash256
    output_root: Hash256
    item_count_in: u64
    item_count_out: u64
    bytes_read: u64
    bytes_written: u64
    fallback_count: u32
    malformed_count: u32
    overflow_flags: u64
    elapsed_us: u64
    deterministic_hash: Hash256
```

### 21.4 Fallback rules

Fallback is explicit and observable:

```text
unsupported feature
resource budget exceeded
queue overflow
malformed input
verification mismatch
GPU/device loss
storage error
cost-model chooses CPU
```

A fallback does not silently change semantics. It emits a reason and preserves stable ordering and hashes.

**The reason list above is frozen as `StageFallbackReason`, and it is the only
sanctioned cross-lane reason vocabulary — but it is not the only reason space
in the tree, and the second one is legitimate.** The DrawIR v3 lane
(`common/ui/draw_ir_v3_execution_route.spl`) carries its own numeric reason
codes, partitioned `100..199` policy / `200..299` denial, precisely to enforce
the `cpu_selected != gpu_fallback` distinction §21.4 is short on. That lane
declined to adopt a cross-lane profile and was right to, for a reason its own
comment did not state; the resolution is recorded here so no consumer lane
re-litigates it.

`DrawIrV3ExecutionProfile` and `StageExecutionProfile` are **not** the same
record and must not be merged. Apply §21.1's own test — the one that kept the
measured-cost `ExecutionProfile` separate — and it returns the same answer
twice: they share no field but `mode`. `StageExecutionProfile` carries
`deterministic`, host and device memory budgets, latency and throughput
targets, `fallback`, `verification` and `allowed_devices`, none of which the v3
record has; the v3 record carries `strict`, `cost_policy_enabled`,
`cost_threshold_commands` and `required_capabilities`, none of which the §21
record has. `required_capabilities` in particular is the DrawIR **backend-tier**
bitset — tier 0 compute passes, tier 1 indirect dispatch — and is a different
vocabulary from the frozen `DeviceMask` bits (scalar CPU, SIMD CPU, GPU,
storage), so it is not even substitutable field-for-field. The v3 record is a
per-submission GPU-offload policy; the §21 record is a per-stage execution
permission. A merge would produce a third record that answers neither question.

`DrawIrV3RouteDecision` is likewise not a profile at all — it is the *after*
half, and its natural counterpart is §21.3's receipt, not §21.1's profile.
It cannot be re-typed onto `StageFallbackReason`, because that enum is closed
at nine variants by the §26 freeze and two of the v3 reasons have no variant in
it: `empty scene` (a policy CPU route with no cost model involved) and
`no device present` (never present, which is not `GPU/device loss` — that
variant means present-then-faulted). A third, `capacity overflow`, maps
ambiguously to either `queue overflow` or `resource budget exceeded`. Forcing
the adoption would be lossy in exactly the direction §21.4 forbids: it would
turn a stated reason into an approximated one.

**What does converge, and is ratified as normative here:** the v3 mode
discriminants and `ExecutionMode` are already byte-identical —
`cpu_reference = 0`, `hybrid_vector_gpu = 1`, `resident_gpu = 2` — in both the
v3 constants and `ExecutionMode`'s frozen variant order. That agreement is
currently a coincidence of two independent numberings and is hereby made a
requirement: **neither side may renumber**, because the boundary crossing
below depends on the identity holding without a translation table.

At the boundary where a DrawIR v3 receipt becomes a `StageReceipt`, the reason
translation is fixed as follows, so seventeen lanes do not each invent one:

| DrawIR v3 reason | `StageFallbackReason` | `requested_mode` vs `mode` |
|---|---|---|
| `none` (0) | `None` | equal |
| `mode is cpu_reference` (100) | `None` | both `CpuReference` |
| `cost below threshold` (101) | `CostModelSelectedCpu` | differ |
| `empty scene` (102) | *no variant* — see below | differ |
| `no device` (200) | *no variant* — see below | differ |
| `missing capability` (201) | `UnsupportedFeature` | differ |
| `capacity overflow` (202) | `ResourceBudgetExceeded` | differ |
| `device fault` (203) | `DeviceLost` | differ |

`capacity overflow` is pinned to `ResourceBudgetExceeded` rather than
`queue overflow` because the DrawIR denial is raised against a declared
capacity limit, not against a full submission queue.

The two gaps are reported, not papered over. `empty scene` and `no device` need
either two added `StageFallbackReason` variants — a wire change to a frozen
enum, which this ratification does not make — or an explicit decision that the
DrawIR receipt is the authoritative record for those two cases and the
`StageReceipt` projection is lossy by design. **Until that decision is taken, a
DrawIR v3 route decision must not be projected onto a `StageReceipt` at all**,
because a lossy projection of a denial reason is the silent fallback §21.4
exists to prevent. That is a decision for the EXEC lane owner.

Layering note, since it is the practical reason the adoption is not merely
undesirable but expensive: `src/lib/common/ui/**` imports nothing from
`common/structural/**` today. Adopting `StageExecutionProfile` would create the
first such edge and would transitively pull in
`common/compute/placement_contracts/semantic.spl` and
`common/structural/receipt/receipt_types.spl` — which itself imports
`contracts.spl` — a substantial dependency cone acquired for one shared field.

Derived from: `common/ui/draw_ir_v3_execution_route.spl` (v3 profile, route
decision and reason constants), `common/structural/execution/profile_types.spl`
(`StageExecutionProfile`, `StageFallbackPolicy`, device/mode bit vocabulary),
`common/structural/receipt/receipt_types.spl` (`StageFallbackReason` and the
selection-provenance fields), and `common/compute/placement_contracts/semantic.spl`
(`ExecutionMode` variant order). Read at origin, not from a lane report.

### 21.5 Cross-domain mode matrix

| Domain | CPU reference | Hybrid | Resident GPU |
|---|---|---|---|
| Simple parser | canonical scalar | SIMD/GPU lex/structure | resident parse arenas, eligible regions |
| Simple optimizer | CPU passes | GPU query/analysis/mutation | resident IR and sidecars |
| Clang | ordinary Clang/LLVM | Clang control + bulk GPU | resident exported AST/IR; Clang semantic fallback |
| HTML parser | ordered CPU | GPU tokenizer + ordered commit | resident tokens/DOM; ordered CPU script commit |
| CSS/style | CPU cascade | GPU candidate/cascade batches | resident indexes/styles |
| layout | CPU algorithms | cost-selected islands | supported islands resident GPU |
| paint/composite | CPU/Engine2D reference | GPU raster/composite | resident display/texture state |
| SMF linker | CPU | GPU bulk stages | resident object/link/output state |

---

# Part X — MDSOC+ mapping

## 22. Dimensions

### 22.1 Stable dimensions

```text
D_entity
    Source, Token, Syntax, AST, HIR, MIR, Symbol, Object, DOM,
    CSS Rule, Style, Layout Fragment, Paint Item, Tag, Mapping,
    Mutation, Dependency, Placement

D_feature
    Parse, Tag, Query, Weave, Optimize, Resolve, Link, Style,
    Layout, Paint, Event, Profile, Persist

D_transform
    Every compiler and web stage boundary, including sidecar mapping
```

### 22.2 Selection dimensions

```text
D_target
    CPU scalar, CPU SIMD, CUDA, Vulkan compute, HIP, future accelerator

D_mode
    CPU reference, hybrid vector/GPU, resident GPU

D_storage
    host, pinned host, shared device, local device, SSD CAS, direct storage

D_assurance
    fast, deterministic, CPU oracle, differential, fault injection

D_mutation
    observe, annotate, instrument, rewrite, optimize

D_incrementality
    full, changed-region, snapshot delta

D_trust
    trusted compiler input, untrusted source/object, sandboxed web content
```

These selection dimensions belong in capability manifests, dependency injection, and generated architecture bindings. They must not create a directory cross-product such as `gpu/resident/deterministic/css/...`.

## 23. New MDSOC+ ports

```simple
interface TagIndexPort
interface OriginMappingPort
interface QueryExecutionPort
interface MutationPlanningPort
interface MutationCommitPort
interface InvalidationPort
interface PlacementPort
interface StageExecutionPort
interface ArtifactStorePort
interface VerificationPort
```

Existing parsing, optimization, codegen, linking, and module-loading ports compose these instead of embedding backend-specific state.

## 24. Virtual capsules

Recommended capsules:

```text
compiler.structural
    IDs, tags, mappings, query, mutation, invalidation contracts

compiler.parse
    Simple ParseDialect + parser adapters

compiler.aop
    pointcut frontend + advice mutation templates

compiler.optimize
    optimizer manifests + QueryIR/MutationIR adapters

compiler.link.smf
    SMF ResolveProfile and emitters

clang.bridge
    AST/LLVM adapters

web.dom
    HTML parser, DOM snapshots, DOM mutation

web.css
    CSS parser, selector QueryIR, StyleLinker, cascade

web.layout
    layout islands and profiles

platform.execution
    mode selection, cost, receipts, fallback

platform.placement
    Object VM, store, placement backends
```

## 25. Proposed source placement

Respect the current numbered compiler layers and current canonical browser location. The exact library-family façade generation should follow repository policy, but the ownership boundaries should resemble:

```text
src/lib/common/structural/
    identity/
    tagmap/
    mapping/
    query/
    mutation/
    invalidation/
    contracts/

src/lib/common/compute/
    execution/
    gpu_flow/
    placement_contracts/

src/lib/<canonical-runtime>/gpu/
    object_vm/
    store/
    placement_backends/

src/compiler/00.common/structural_contracts/
src/compiler/10.frontend/canonical_ast/
src/compiler/10.frontend/structural_adapter/
src/compiler/60.mir_opt/structural_adapter/
src/compiler/70.backend/linker/gpu_smf/
src/compiler/85.mdsoc/feature/tagging/
src/compiler/85.mdsoc/feature/query/
src/compiler/85.mdsoc/feature/mutation/
src/compiler/85.mdsoc/feature/placement/
src/compiler/85.mdsoc/transform/**/sidecars/

src/lib/<canonical-runtime>/gpu/browser_engine/dom/
src/lib/<canonical-runtime>/gpu/browser_engine/css/
src/lib/<canonical-runtime>/gpu/browser_engine/layout/
src/lib/<canonical-runtime>/gpu/browser_engine/render_session/

tools/clang-bridge/
    frontend/
    transformer/
    llvm_pass/
```

Do not manually copy the implementations into every GC/no-GC and sync/async library family. Keep pure contracts and data formats common; generate or write thin family façades around one canonical implementation.

---

# Part XI — Parallel implementation plan

## 26. Contract-freeze phase

Before subsystem development, freeze these versioned artifacts:

```text
EntityRef / EntityKey / SnapshotId
TagSchema and tag encoding
MappingKind and compressed mapping format
QueryIR bytecode and capture format
MutationIR and conflict order
DirtyMask and dependency edge format
StageReceipt and VerificationReceipt
PlacementRequest / PlacementPlan / lease rules
ExecutionProfile and capability vocabulary
ResolveProfile and SpatialLayoutProfile contracts
```

Deliverables:

- language-neutral binary/SDN schema;
- Simple types;
- Rust/C++ bridge types where needed;
- CPU reference serializers/deserializers;
- golden vectors;
- compatibility/versioning policy.

No agent begins backend-specific implementation against an unfrozen private structure.

## 27. Parallel lanes and exclusive ownership

| Lane | Exclusive ownership | Deliverable |
|---|---|---|
| ID-TAG | `structural/identity`, `structural/tagmap` | IDs, tag schemas, dense/sparse storage, indexes |
| MAP | `structural/mapping` | many-to-many provenance, source tracing, compression |
| QUERY | `structural/query` | QueryIR compiler/runtime, dialect extension API |
| MUTATE | `structural/mutation` | plans, conflict resolution, snapshots, receipts |
| INVALIDATE | `structural/invalidation` | dependency graph, dirty propagation, explain traces |
| EXEC | `compute/execution` | modes, capabilities, cost model, planner, receipts |
| PLACE | `gpu/object_vm`, `gpu/store`, placement backends | handles, leases, CAS, staged/direct/device modes |
| PARSE | generic parser framework | lex/structure/grammar/action runtime, incremental parse |
| SIMPLE | Simple frontend/AOP/optimizer adapters | QueryIR pointcuts, MutationIR weaving, structural optimizer |
| CLANG-AST | Clang frontend/export/transformer | AST export, matcher adapter, source mutations |
| LLVM | LLVM pass plugin/profile | IR tags, queries, mutations, remarks, mappings |
| HTML-DOM | HTML parser and DOM snapshot | tokenizer/tree adapter, DOM SoA, DOM mutation |
| CSS-STYLE | CSS parser/style resolver | selector IR, indexes, cascade, CSS mutation |
| LAYOUT | spatial layout | islands, profiles, incremental/GPU planners |
| LINK | ResolveCore and SMF linker | graph resolver, CPU/hybrid/resident SMF paths |
| WEB-RENDER | render-session integration | stage orchestration, paint/composite, event boundary |
| VERIFY | tests and benchmarks only | oracles, parity, fault injection, performance evidence |

### Shared-file rule

Only one integration owner modifies:

```text
root __init__.spl/mod.spl exports
compiler driver and CLI
MDSOC global binding/selection
browser production composition root
capability manifest generation
```

Subsystem lanes submit integration descriptors rather than editing these files directly.

## 28. Dependency graph

```text
Contract freeze
   ├─ ID-TAG ─┬─ QUERY ─┬─ SIMPLE
   │          │         ├─ CLANG-AST
   │          │         ├─ CSS-STYLE
   │          │         └─ LINK
   ├─ MAP ────┤
   ├─ MUTATE ─┼─ SIMPLE / CLANG / HTML-DOM / CSS-STYLE
   ├─ INVALIDATE ─ CSS-STYLE / LAYOUT / compiler incremental
   ├─ EXEC ───┬─ PARSE / LINK / LAYOUT / WEB-RENDER
   └─ PLACE ──┴─ all resident-GPU lanes

HTML-DOM + CSS-STYLE + INVALIDATE -> LAYOUT -> WEB-RENDER
SIMPLE + LLVM + LINK -> compiler end-to-end
```

## 29. Waves

### Wave 0 — Representation repair and contracts

- flat source buffers, span tokens, interning, SoA syntax;
- DOM/CSS canonical schema draft;
- all frozen contracts and golden vectors;
- CPU-only implementations of ID, tags, mappings, QueryIR, MutationIR.

**Gate:** no GPU work may encode current object-heavy token/AST/DOM structures.

### Wave 1 — CPU reference platform

- QueryIR evaluator;
- Mutation transaction and immutable snapshot store;
- dependency/invalidation engine;
- CPU GraphResolveCore;
- CPU SpatialLayoutProfile adapter over current layout;
- MDSOC sidecar ports.

**Gate:** deterministic hashes and rollback tests pass.

### Wave 2 — Simple AOP and optimizer migration

- compile pointcuts to QueryIR;
- implement missing selectors;
- emit advice as MutationIR;
- convert optimizer source patterns to structural queries;
- structured optimization receipts and source mappings.

**Gate:** current AOP tests plus new structural selectors pass with zero inactive overhead.

### Wave 3 — Execution and placement foundation

- `gpu_flow` primitives;
- Object VM handles/leases;
- staged SSD backend;
- placement planner;
- mode/cost/fallback selection.

**Gate:** bounded host memory, eviction/recovery, stale-handle, and fault-injection tests pass.

### Wave 4 — Parser acceleration

- SIMD structural indexes;
- GPU lexical summaries/scans;
- Simple token/structure path;
- CSS token/parser path;
- HTML tokenizer path;
- incremental changed-region infrastructure.

**Gate:** byte/token/diagnostic parity with CPU and crossover benchmarks.

### Wave 5 — Clang and LLVM bridge

- pinned Clang FrontendAction and flat AST export;
- matcher and Transformer adapters;
- LLVM pass plugin and pass instrumentation;
- optimization remarks/profile mapping;
- source/IR AOP proof-of-concept.

**Gate:** Clang/LLVM regression subset, macro-location tests, and mutation round-trip tests.

### Wave 6 — DOM/CSS incremental engine

- DOM snapshot/delta transaction;
- selector invalidation features;
- CSS mutation;
- computed-style sharing and style-difference classification;
- full-recompute oracle comparison.

**Gate:** every incremental result equals full recomputation for the same snapshot.

### Wave 7 — SMF linker and Web resolver

- GPU-capable ResolveCore primitives;
- SMF decode/resolve/reachability/layout/relocation;
- StyleLinker/resource profile;
- source-to-output mappings.

**Gate:** deterministic SMF parity and Web resolution parity.

### Wave 8 — Incremental spatial layout

- layout-island discovery;
- dirty-island scheduling;
- block/flex/grid GPU batches;
- CPU fallback for text/irregular contexts;
- layout mapping and hit-index updates.

**Gate:** geometry/tree/pixel oracle parity and profitable cost thresholds.

### Wave 9 — Resident-GPU integration

- keep source/IR/DOM/style/layout/link arenas resident;
- compact CPU command/receipt boundary;
- direct-storage backend where supported;
- end-to-end Simple compiler and Web renderer resident sessions.

**Gate:** cross-mode deterministic output, bounded host RSS, crash recovery, and no silent fallback.

---

# Part XII — Verification and acceptance

## 30. Core structural verification

### 30.1 Identity

- stale snapshot/entity references fail;
- durable keys resolve only against compatible artifact/schema versions;
- hash collisions are verified by full identity bytes;
- no raw pointer is persisted.

### 30.2 Tags

- dense and sparse encodings return identical results;
- merge policies are deterministic;
- demand-disabled tags allocate no storage;
- inverted indexes match direct scans.

### 30.3 Mappings

Test one-to-one, split, merge, clone, inline, weave, fold, eliminate, style, layout, and link cases. Source tracing must preserve all required origins through multiple stages.

### 30.4 QueryIR

- scalar, SIMD, CUDA, and Vulkan evaluators produce identical stable entity/capture order;
- legacy Simple pointcuts and new QueryIR agree on existing cases;
- AST Matcher adapter agrees with canonical Clang AST evaluation for the supported subset;
- CSS selector evaluator is tested against standards conformance fixtures.

### 30.5 MutationIR

- operation ordering is deterministic;
- conflicts never depend on thread scheduling;
- stale-revision commit fails;
- failed validation leaves the original snapshot unchanged;
- receipts exactly explain applied, skipped, and rejected operations.

## 31. Compiler/AOP/optimizer verification

- all existing AOP system scenarios;
- new `within`, `attr`, call, assignment, decision, condition, and error selectors;
- around-advice `proceed` cardinality and exceptional paths;
- no-weaving binary/MIR parity when AOP disabled;
- optimizer before/after semantic equivalence;
- pass-order determinism;
- profile and optimization-remark source mapping;
- multi-file cache invalidation closure;
- CPU/hybrid/resident artifact hash parity.

## 32. Clang verification

- supported Clang-major matrix;
- preprocessing/macro spelling and expansion locations;
- templates and instantiation identity;
- AST Matcher versus QueryIR captures;
- source Replacements compile cleanly;
- LLVM verifier after each IR mutation;
- optimization remark and debug-location preservation;
- differential compilation and runtime tests against unmodified Clang.

## 33. HTML/CSS/DOM verification

- HTML tokenizer/tree parity with CPU reference;
- mutation transactions under script/event ordering;
- selector matching and cascade conformance;
- CSSOM insert/delete/replace rules;
- DOM class/ID/attribute/structure mutation invalidation;
- custom-property dependency invalidation;
- incremental style equals full recomputation;
- untrusted-input quotas and checked arithmetic.

## 34. Layout and renderer verification

- layout tree and fragment geometry equality against CPU oracle;
- block/flex/grid/table/absolute/scroll fixtures;
- text shaping and baseline fixtures;
- incremental layout equals full layout;
- paint/display-list and hit-test parity;
- pixel-diff thresholds plus exact structural oracles;
- unchanged-frame reuse and resource reclamation.

## 35. Linker verification

- malformed SMF bounds and overflow rejection;
- symbol resolution order and duplicate diagnostics;
- reachability/dead stripping;
- relocation formulas and overflow rules;
- deterministic output bytes;
- source/object/symbol/output-range mappings;
- CPU/hybrid/resident parity.

## 36. Object VM and placement verification

- state-machine transition faults;
- duplicate miss coalescing;
- pin/in-flight eviction prevention;
- dirty checkpoint and crash recovery;
- SSD corruption and partial-journal recovery;
- staged/direct backend parity;
- fixed host-memory budget as corpus size grows;
- placement cost estimate calibration.

## 37. Performance acceptance

A speedup claim includes the complete path:

```text
file discovery
hashing
SSD read
host staging or direct transfer
allocation/residency
kernel execution
synchronization
fallback
readback/receipt
SSD output
commit
```

No kernel-only measurement qualifies as an end-to-end improvement.

Each stage records CPU/GPU crossover curves by item count, bytes, structural complexity, and cache state. `auto` dispatch uses measured thresholds and confidence bounds.

---

# Part XIII — Feasibility and risk

## 38. Feasibility matrix

| Capability | Assessment | Initial treatment |
|---|---|---|
| typed side-table tags and mappings | Green | implement first |
| QueryIR CPU/SIMD/GPU set operations | Green | shared foundation |
| transactional source/IR/DOM/CSS mutations | Green | CPU reference first |
| Simple AOP structural selectors | Green | early migration |
| optimizer structural source/MIR matching | Green | early migration |
| SIMD/GPU lexing and structural indexing | Green | early acceleration |
| CSS selector candidate matching/cascade batching | Green | hybrid path |
| DOM/CSS exact invalidation | Green/Amber | CPU first, GPU later |
| SMF hash/sort/group/scan/relocation | Green | first GPU linker |
| arena/chunk object placement with SSD CAS | Green | core subsystem |
| GPU Simple region parser | Amber | bounded grammar regions |
| Clang AST bulk querying and safe rewrites | Green/Amber | pinned adapter |
| selected LLVM IR GPU analyses/mutations | Amber | pass by pass |
| homogeneous flex/grid/block GPU layout | Amber | cost-selected islands |
| fully GPU browser tree builder with script interaction | Red initially | ordered CPU commit |
| complete C++ frontend/Sema on GPU | Red initially | Clang oracle/fallback |
| transparent SSD-backed persistent raw pointers | Red | explicitly reject |

## 39. Principal risks and mitigations

### Risk: framework over-generalization

**Mitigation:** share data and execution primitives, not domain semantics. Keep Query dialects, Resolve profiles, and Layout profiles explicit.

### Risk: tag/mapping memory becomes a new blowup

**Mitigation:** demand-driven schemas, dense/sparse specialization, compressed shards, arena-level placement, and hard metadata budgets.

### Risk: mutation conflicts become nondeterministic

**Mitigation:** immutable snapshots, total stable ordering, declared effect summaries, and domain-specific conflict resolvers.

### Risk: GPU overhead exceeds useful work

**Mitigation:** CPU reference remains first-class; cost estimates include transfer and synchronization; small tasks stay CPU/SIMD.

### Risk: Clang integration breaks with versions

**Mitigation:** pin supported majors, version adapter schemas, and run Clang/LLVM regression subsets.

### Risk: web incremental invalidation misses a dependency

**Mitigation:** run incremental result against full recomputation in tests and sampled assurance mode; publish invalidation explain traces.

### Risk: GPU-resident data is corrupted or lost

**Mitigation:** immutable SSD artifacts, host-authoritative commit manifests, receipts, lease epochs, checkpoint policy, and CPU recovery.

---

# Part XIV — Recommended first production slice

## 40. Slice A: structural core and Simple AOP

Deliver first:

```text
EntityRef / EntityKey / SnapshotId
TagMap
MappingGraph
CPU QueryIR
CPU MutationIR
MDSOC sidecar ports
Simple pc{} -> QueryIR
attr/within selectors
AOP MutationIR weaving
```

This immediately removes matcher duplication, makes AOP structurally extensible, and creates the foundation for all later work.

## 41. Slice B: DOM/CSS invalidation

Deliver next:

```text
DOM stable IDs and snapshots
CSS selector QueryIR
selector feature indexes
DOM/CSS mutation transactions
DirtyMask and style-difference classification
full-recompute oracle
```

This improves current browser architecture even before GPU acceleration.

## 42. Slice C: placement and hybrid acceleration

Then deliver:

```text
gpu_flow primitives
Object VM handles/leases
bounded staged SSD backend
SIMD structural indexes
GPU lexer/CSS candidate/linker primitives
cost-based hybrid scheduler
```

## 43. Slice D: Clang/LLVM and resident pipelines

After contracts and parity are stable:

```text
Clang AST export/matcher/Transformer bridge
LLVM pass plugin/remarks/provenance
SMF resident linker
resident DOM/style/layout batches
resident multi-file Simple compilation
```

---

# 44. Final target architecture

```text
                                HOST CONTROL / TRUST / COMMIT
┌─────────────────────────────────────────────────────────────────────────────┐
│ driver │ sandbox/broker │ Clang/Sema fallback │ event/script order          │
│ policy │ capability selection │ diagnostics │ receipts │ manifest commit    │
└──────────────────────────────────┬──────────────────────────────────────────┘
                                   │ IDs, plans, deltas, receipts
                                   ▼
                           STRUCTURAL COMPUTE PLANE
┌─────────────────────────────────────────────────────────────────────────────┐
│ Identity │ TagMap │ MappingGraph │ QueryIR │ MutationIR │ InvalidationGraph │
│ ParseRuntime │ GraphResolveCore │ SpatialLayout │ ExecutionPlanner          │
└───────────────┬────────────────────────┬───────────────────────┬─────────────┘
                │                        │                       │
                ▼                        ▼                       ▼
       SIMPLE / CLANG PIPELINE      HTML / CSS / DOM       SMF / RESOURCE LINK
       AST-HIR-MIR-LLVM             style-layout-paint      resolve-layout-reloc
                │                        │                       │
                └────────────────────────┴───────────────────────┘
                                         │
                                         ▼
                             GPU OBJECT / PLACEMENT PLANE
┌─────────────────────────────────────────────────────────────────────────────┐
│ Object descriptors │ leases │ VRAM arenas │ queues │ scans/sort/group       │
│ staged I/O │ optional direct storage │ optional device-initiated storage    │
└──────────────────────────────────┬──────────────────────────────────────────┘
                                   ▼
                    SSD CAS + manifests + journal + checkpoints
```

The central architectural outcome is not merely "a GPU parser" or "a GPU linker." It is a single, deterministic, provenance-preserving structural-compute system in which:

- parsers emit queryable tags and mappings;
- AOP and optimizers select entities through one structural query model;
- all changes are transactions with exact invalidation and receipts;
- Clang and LLVM participate through adapters rather than forks;
- DOM and CSS mutation reuse the same transaction/invalidation substrate;
- HTML spatial layout is independently schedulable by formatting-context islands;
- SMF and Web resource resolution reuse graph primitives without sharing semantics;
- CPU, hybrid SIMD/GPU, and resident-GPU modes preserve the same observable result;
- Object VM placement keeps large multi-file/compiler/browser state off host RAM and reloads it from immutable SSD artifacts only when required.

---

# Appendix A — Interface dependency index

```text
IdentityPort
    used by every subsystem

TagReadPort / TagWritePort
    used by parser, AOP, optimizer, Clang, DOM/CSS, layout, linker, placement

MappingReadPort / MappingWritePort
    used by compiler transforms, profile attribution, DOM/style/layout, linker

QueryExecutionPort
    used by AOP, optimizer, Clang matching, CSS selector matching, diagnostics

MutationPlanningPort / MutationCommitPort
    used by AOP, optimizers, source transforms, DOM/CSSOM, linker rewrites

InvalidationPort
    used by incremental compiler, DOM/CSS/style/layout/paint, resource changes

StageBackend
    implemented by CPU, SIMD, CUDA, Vulkan, HIP-specific executors

PlacementBackend
    implemented by staged, direct-storage, device-initiated transports

ParseDialect
    implemented by Simple, CSS, HTML, optional constrained C

ResolveProfile
    implemented by SMF, Clang offload, Web resources/style definitions

SpatialLayoutProfile
    implemented by block, inline, flex, grid, table, positioned, scroll
```

# Appendix B — Example AOP rule lowering

Source:

```simple
on pc{ execution(* service.*(..)) & attr(transactional) }
use trace_transaction before priority 100
```

Normalized plan:

```text
QueryProgram
    seed aop.join.execution
    filter semantic.qualified_name glob service.*
    filter aop.attr == transactional
    capture join

MutationTemplate
    for each capture(join), stable source order:
        InsertMirBefore(target=join.entry,
                        call=trace_transaction,
                        priority=100)
        map advice declaration -> inserted call as WovenFrom
        map original join -> inserted call as WovenFrom
        invalidate MIR, optimization, codegen, link
```

# Appendix C — Example CSS/DOM mutation

Mutation:

```text
node #42: class "button" -> "button primary"
```

Derived work:

```text
1. DOM snapshot delta and class index update.
2. Select invalidation programs depending on class(primary).
3. Evaluate candidates beginning at node #42 and required relationship scopes.
4. Recompute cascade for affected nodes.
5. Compare style fingerprints.
6. Suppose only background-color changes:
       dirty Paint for node #42; retain Layout.
7. Emit MutationReceipt and new document/style snapshot.
```

# Appendix D — Example execution policy in SDN style

```sdn
execution_profile compiler_release:
    mode: hybrid_vector_gpu
    deterministic: true
    host_memory_budget: 256 MiB
    device_memory_budget: 12 GiB
    fallback: cpu_reference
    verification: sampled_oracle

execution_profile web_interactive:
    mode: hybrid_vector_gpu
    deterministic: true
    latency_target: 8 ms
    fallback: cpu_reference
    layout:
        gpu_min_estimated_work: 50000
        retain_gpu_dom: true

execution_profile compiler_gpu_resident:
    mode: resident_gpu
    deterministic: true
    host_memory_budget: 128 MiB
    storage_backend: direct_or_staged
    fallback: hybrid_vector_gpu
```

# Appendix E — Primary sources consulted

- Clang LibTooling, AST Matchers, Transformer framework, and offloading design documentation.
- LLVM New Pass Manager, pass instrumentation, metadata, debug information, and optimization-remark documentation.
- AspectC++ and Clava publications and project documentation.
- simdjson architecture and ParPaRaw GPU parsing research.
- WHATWG HTML parsing model and CSS Syntax specifications.
- Chromium/Blink style invalidation, lifecycle, and paint architecture documentation.
- Servo and parallel-layout research.
- CUDA virtual memory and GPUDirect Storage documentation.
- BaM, GPUfs, ActivePointers, and DynaSOAr research.
- mold linker design and NVIDIA device-linking documentation.
- Current Simple repository compiler MDSOC, AOP, optimizer, parser-memory, browser, layout, and linker documentation and source.

---

# Appendix F — Summary of principal additions over the superseded plan

This document expands the previous GPU parser/linker/Object-VM proposal into a
unified tagged structural-compute architecture for the Simple compiler,
Clang/LLVM, HTML/CSS/DOM, spatial layout, rendering, linking, and SSD-backed
GPU residency. It extends the existing compiler MDSOC structure rather than
adding another orchestration layer: Simple already has feature ports for all
compiler stages and stage-boundary transforms, while its primary entities remain
in the numbered compiler layers, so the updated design adds sidecar tag,
mapping, query, mutation, invalidation, execution, and placement ports at those
boundaries.

1. **Shared tagging and mapping framework** — compact `EntityRef` for GPU hot
   paths, durable `EntityKey` for caches/diagnostics/AST/source links and
   cross-revision matching, typed namespaced `TagMap` side tables, many-to-many
   `MappingGraph` provenance, and demand-driven dense columns, bitsets, sparse
   records and inverted indexes. Tags are not added as fields to every AST or DOM
   node, which preserves the SoA/arena memory strategy already recommended by
   Simple's parser-memory research (per-character objects, copied strings and
   unreclaimed per-file objects were identified as major causes of current memory
   growth).

2. **One QueryIR with domain dialects** — a common engine underlies Simple `pc{}`
   pointcuts, optimizer structural patterns, Clang AST matching, LLVM IR
   matching, DOM queries, CSS selectors, linker symbol/reference queries and
   layout dependency queries. Each domain keeps its own syntax and semantics but
   compiles into a shared indexed set-and-traversal representation. This closes
   two current gaps: the AOP core parses selectors such as `attr` and `within`
   but leaves some deliberately nonmatching, and the optimizer's source-level
   plugin path can still select opportunities by line-oriented text containment.

3. **Transactional MutationIR** — AOP weaving, compiler optimization, Clang
   rewrites, LLVM transformations, DOM changes, CSSOM changes, linker rewrites
   and placement hints all run as immutable snapshot → structural query →
   deterministic MutationPlan → validation → conflict resolution → apply into new
   arenas → provenance update → exact invalidation → verification → commit. This
   turns the around-advice requirement that `proceed()` execute exactly once into
   an explicit control-flow verifier.

4. **Performance-mutation framework** — stable optimization points and a feedback
   loop shared by Simple, Clang, LLVM, CSS, layout and linker optimization, with
   structured tags for hotness, vectorization suitability, GPU suitability,
   transformation legality, missed-optimization reasons and measured latency.

5. **Clang/LLVM bridge with three modes** — built on the official extension
   surfaces (LibTooling/`FrontendAction`, AST Matchers, Transformer/Replacements,
   `PassBuilder` plugins, pass instrumentation, metadata/debug locations,
   optimization remarks). The document explicitly avoids claiming that
   production-complete C++ preprocessing, templates, concepts and Sema can
   immediately become all-GPU; the realistic aggressive mode is almost all
   eligible data-plane work resident on GPU with Clang retaining semantic
   authority and fallback, and a constrained preprocessed-C frontend as the
   experimental full-GPU target.

6. **HTML/CSS/DOM mutation architecture** — SoA DOM and CSS rule arenas, stable
   document-local node identities, GPU/SIMD HTML tokenizer with an ordered
   browser-compatible tree-builder commit, a static-template mode with greater
   parallel subtree construction, CSS selectors compiled to QueryIR, bounded DOM
   and CSS mutation command buffers, and immutable DOM/style revisions.
   Invalidation is redesigned around selector feature indexes rather than
   rerunning parse/CSS/style/layout/paint after every accepted change.

7. **Independent HTML spatial layout manager** — clearly separated from GPU
   memory placement: `LayoutInputSnapshot`, formatting-context `LayoutIsland`s,
   block/inline/flex/grid/table/positioned/scroll/replaced profiles,
   intrinsic-size and containing-block dependency graphs, topological waves and
   bounded fixed points, incremental dirty-island scheduling, a CPU text-shaping
   port, and mandatory per-island execution cost estimates (parallel-layout
   research shows scheduling overhead can exceed the benefit on small or
   irregular pages).

8. **Generic resolver without conflating linker and layout** — `GraphResolveCore`
   shares definitions, references, stable group resolution, reachability,
   constraint propagation, scan-based placement, patch generation and receipts,
   with separate `SmfLinkProfile`, `ClangOffloadLinkProfile` and
   `WebResourceLinkProfile`; HTML spatial layout remains a separate
   `SpatialLayoutProfile`. Native ELF/Mach-O/PE stays delegated to established
   native linkers initially because mold does not emit SMF.

9. **GPU Object VM placement framework** — `PlacementRequest`, `PlacementPlan`,
   `PlacementBackend`, `ResidentView` leases, prefetch, checkpoint, eviction,
   recovery, and affinity/lifetime hints across the residency tiers. The portable
   backend uses bounded pinned staging; direct SSD-to-GPU transfer is optional and
   GPU-initiated NVMe/cache behavior is experimental. The placement unit is an
   arena or shard — never an individual AST, DOM or layout node — so metadata
   overhead stays bounded.

10. **Parallel implementation structure** — seventeen non-overlapping lanes
    (ID-TAG, MAP, QUERY, MUTATE, INVALIDATE, EXEC, PLACE, PARSE, SIMPLE,
    CLANG-AST, LLVM, HTML-DOM, CSS-STYLE, LAYOUT, LINK, WEB-RENDER, VERIFY) with
    a single integration owner for exports, compiler driver/CLI, global MDSOC
    bindings, browser composition roots and capability-manifest generation, run
    across ten gated waves. GPU and SIMD parsing are based on structural-first
    parsing and chunk lexical-state summaries rather than attempting to execute
    the existing branch-heavy, object-oriented parser unchanged on a GPU.
