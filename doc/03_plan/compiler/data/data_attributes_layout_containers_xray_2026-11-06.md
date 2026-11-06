# Simple: Unified Data Attributes, Layouts, Adaptive Containers, and XRay

## Compiler, interpreter, and BuildRunner design and implementation plan

**Date:** 2026-11-06  
**Revision:** 1.0 — consolidated final report for this conversation, including the expanded AoS/SoA and XRay request  
**Repository:** `ormastes/simple`  
**Current source-inspection pin:** `0e4d613ab46a3af12e2111c480b1c1db9f6dc513`  
**Earlier inspection retained for comparison:** `97700b29e10675867891503f1e634b50a192356d`  
**Status:** Accepted plan; implementation in progress  
**Suggested repository destination:** `doc/03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md` (proposed, not written to the repository).

This report completes the attribute-support request and the subsequent request to make three data families consistent: **record collections with AoS/SoA layouts, adaptive sets/maps, and typed node trees**. It specifies one policy and profiling framework without pretending that their different physical choices are the same operation.

New API names, attributes, configuration keys, diagnostics, and test IDs below are **proposed contracts unless explicitly identified as existing**. Illustrative code is not a claim that the current compiler accepts it. Source presence, a design document, and executed qualification evidence are different levels of evidence.

## Contents

1. [Executive decisions and corrections](#1-executive-decisions-and-corrections)
2. [Existing support and remaining integration gaps](#2-existing-support-and-remaining-integration-gaps)
3. [One logical schema and generated field access](#3-one-logical-schema-and-generated-field-access)
4. [Whole-node initialization and removal](#4-whole-node-initialization-and-removal)
5. [Node identity, regions, and topology](#5-node-identity-regions-and-topology)
6. [AoS, SoA, and related layouts](#6-aos-soa-and-related-layouts)
7. [Set and map algorithms](#7-set-and-map-algorithms)
8. [Unified source and SDN configuration](#8-unified-source-and-sdn-configuration)
9. [Aspects and logical get/set events](#9-aspects-and-logical-getset-events)
10. [Shared XRay profiling architecture](#10-shared-xray-profiling-architecture)
11. [Profile selection and safe switching](#11-profile-selection-and-safe-switching)
12. [Compiler, interpreter, and BuildRunner integration](#12-compiler-interpreter-and-buildrunner-integration)
13. [Cache, TLDR, reverse-reference, and persistence rules](#13-cache-tldr-reverse-reference-and-persistence-rules)
14. [Implementation work packages](#14-implementation-work-packages)
15. [Acceptance, performance, and formal verification](#15-acceptance-performance-and-formal-verification)
16. [Sources and completion boundary](#16-sources-and-completion-boundary)

## 1. Executive decisions and corrections

### 1.1 Binding design decisions

1. **Ordinary field syntax is the public API.** A logical read such as `node.source_span` and a write such as `node.source_span = span` resolve to generated typed access operations. A physical struct field, SoA column, sparse side table, or admitted computed property can implement the operation.
2. **Attributes may be declared in SPL or SDN build configuration.** Both enter one schema resolver before name/type checking, accessor generation, and aspect matching. Configuration is a typed build input, not an untyped runtime dictionary.
3. **One canonical attribute name has one exact type within one tree schema.** Conflicting declarations fail. A common machine representation does not make `RegionId`, `ObjId`, `TypeId`, and `SymbolId` interchangeable.
4. **Initialization belongs to the whole node: `NotInit<Node>`.** Do not wrap every attribute in `NotInit<T>`. Construction records internally which required fields have been assigned; only successful finalization yields a usable node.
5. **Pending construction must be completed or explicitly discarded.** Normal scope exit with an unresolved obligation is diagnosed. Removal of a published node is a separate lifecycle operation; stale aliases do not magically become pending builders.
6. **No mandatory user-visible tag/kind field.** Typed node views and schema/pool metadata provide type identity. Existing internal AST discriminator arrays and serialized type metadata may remain where needed.
7. **Do not introduce implementation inheritance.** The earlier `class Child(Parent)` and `class Child : Parent` examples were inappropriate as claims about supported Simple. Use composition, traits, forwarding, and typed node views. [R01]
8. **Reuse the existing layout and collection owners.** Compose `StorageLayoutPlanV1`, the current CollectionPlan selection machinery, adaptive containers, and the existing `.sprof` pipeline. Do not introduce another layout enum, profiler database, scheduler, or optimizer authority.
9. **Use a shared tracing facade, not direct LLVM calls in application/data APIs.** Preserve the staged XRay plan: Linux LLVM provider, Linux Simple-owned provider, then Windows Simple-owned provider. Capabilities determine support; public data/profile/config contracts remain stable across providers. [D05]
10. **Profiles rank safe candidates; they do not establish safety.** They cannot prove that an unobserved field is unused, a map never mutates, aliases do not exist, or a critical operation has a bounded worst case.
11. **Default compiler/cache adoption is next-build or next-instance.** Existing exclusively owned adaptive-map transitions remain supported. General node/layout live migration is separately admitted and opt-in.
12. **XRay handlers never migrate storage.** They record bounded observations. A policy/controller evaluates them outside callbacks and applies a validated plan at an appropriate boundary.

### 1.2 The three families share policy, not an algorithm enum

| Data family | Logical contract | Physical choices | Useful profile evidence |
|---|---|---|---|
| Record sequence | Ordered elements, duplicates, typed fields | AoS, SoA, later qualified AoSoA/hot-cold layouts | Field co-access, scan patterns, working-set size, conversion cost |
| Set/map | Exact membership or key/value lookup; declared ordering/equality guarantees | Linear array, hash, ordered tree; later sorted array, other hash families, direct index | Cardinality, lookup/update mix, hit/miss, comparisons, collisions, iteration |
| Node tree/graph | Typed nodes, required fields, topology constraints, identity and lifetime | Per-type pools; dense/sparse attributes; row/column layout; compact adjacency | Attribute occupancy/co-access, traversal, degree, churn, region lifetime |

The physical decisions are orthogonal:

- **Layout:** how records and fields are placed in memory.
- **Index algorithm:** how a key or ID locates a value.
- **Occupancy:** whether all applicable slots or only present values are materialized.
- **Topology encoding:** how edges and child lists are represented.
- **Application mode:** when a selected representation takes effect.

A hash map can have AoS entries or separated key/value/control arrays. A SoA node store can use an array directory and sparse hash-backed diagnostic attributes. An ordered list of children cannot silently become an unordered set.

### 1.3 Relationship to earlier plans

| Prior work | Retained | Updated here |
|---|---|---|
| Adaptive collections [D01] | Per-site policies, semantic eligibility, `.sprof`, bounded switching | Shared node-attribute schema and XRay-provider integration |
| Typed dataframe/CollectionPlan [D02] | Typed logical operations and separate layout/index/execution choices | Managed field accesses become common optimizer/profiler inputs |
| Cache/SCV and resource helpers [D03], [D04] | Immutable generations, exact identities, first-producer sharing, bounded resources | Schema/layout/profile identity, node-region handles, safe storage transitions |
| Aspect/visibility plan [D06] | Existing AOP owners, explicit debug/release policy, no invisible interface change | Its earlier exclusion of generated getters/setters is superseded for this requested data work |
| Staged XRay plan [D05] | Stable public V1 facade; provider capability gates; resident instrumentation; raw versus paired events | Predeclare a versioned data-observation extension and integrate all three families |

The later XRay plan's **resident provider/instrumentation policy** takes precedence over the earlier suggestion that a debug provider should be hot-unloaded. Releasing a profile session does not authorize unmapping code or metadata. This report does not implement the broader Windows tracing port, a new exception system, or arbitrary dynamic around-advice.

## 2. Existing support and remaining integration gaps

### 2.1 Source audit summary

| Area | Evidence found | Limit and required work |
|---|---|---|
| Compiler AST storage | Expression, statement, and declaration pools use parallel arrays with explicit owner accessors. [R02] | Generated schema-based access is not established; existing debug-gated generation checks are not a complete lifetime guarantee. |
| Cached AST | `FileAstV1` is pointer-free and stores an array of node records plus payload tables. [R03] | This is **AoS node records**, not proof that the cache format already uses SoA. Preserve/version codecs. |
| Implicit properties | Rust interpreter resolves real fields, then getter/boolean getter and method conventions. Pure-Simple interpreter has distinct indexed field-access paths. [R04] | Do not assume cross-engine parity or automatic storage-backed getter generation. Missing managed fields must never default to zero. |
| HIR fields | Resolved field types, defaults, visibility and low-level placement facts exist. [R05] | Add logical attribute/schema identity and generated access metadata without discarding existing volatile/fixed-address constraints. |
| Layout vocabulary | `StorageLayoutPlanV1` and AoS/SoA/AoSoA/Grouped/Tiled/Packed/FactoredIndex/ExternalFixed exist. [R06] | An enum value is not proof of backend implementation. |
| Layout mapping | Overflow-checked AoS, SoA, AoSoA and fixed-layout mapping/reference conversion exist. [R07] | Other mappings need specialized implementations and explicit capability admission. |
| Compiler layout lowering | Narrow typed raw-allocation projections and a compiler-private pilot exist. [R08] | This is not universal ordinary-array conversion. Source binding, writes, mixed fields, alias coverage and backend expansion need qualification. |
| Set/map switching | Generic `AdaptiveMap` and `AdaptiveSet` have linear/hash/ordered selection and actual conversion code. [R09] | They are ordinary exclusively mutable containers, not a qualified lock-free shared cache or arbitrary region-migration engine. |
| Actual map algorithms | Generic map uses bucketed separate chaining; ordered map uses an array-indexed AVL tree. [R10] | Do not call the existing ordered backend a B-tree or the hash backend a Swiss table. |
| Source algorithm annotation | `@collection_algorithm` recognizes `auto`, `linear`, `hash`, `ordered` and routes attributed constructors with site/profile data. [R11] | General SDN/schema/layout unification and context isolation are additional work. |
| Typed collection selection | Shared semantic selection has proof/memory gates; a narrow fresh integer-dictionary membership consumer exists. [R12] | General adaptive-container MIR integration is incomplete; saying there is no executable consumer at all would also be wrong. |
| Collection capture | Shared capture ABI and `.sprof` ingestion expose size, lookup, probe, materialization and loop/filter observations; emitter coverage and executable qualification vary by path. [R13] | Existing capture is not XRay; its active global-lock/string-key path cannot be assumed acceptable on a strict low-contention hot path. |
| Field aspects | The current validator marks `get`/`set` as E1507-deferred; MIR generic assignment is not a typed property contract. Accepted `attr(...)` also lacks matching support in the inspected tokenized compiler/interpreter paths. [R14] | Add canonical logical attr events across parser, matcher, compiler, interpreter and tooling. |
| BuildRunner | Parent-owned scheduler has parallel task/status/host arrays and a task-ID dictionary. [R15] | Good migration target, but generated setters must not bypass scheduling/result validation. |
| Region transfer | Versioned region/generation/ownership envelope and no-raw-pointer transfer rules exist. [R16] | A common compiler/runner `ObjId` is not established merely by an engine handle or formal-model carrier. |
| XRay work | Current head includes merged experimental native Windows verification fixtures, beyond the earlier audit. [R18] | Fixture/ABI evidence is not proof that all data events or the complete Simple source-to-XRay runtime path are integrated. |

### 2.2 Specific layout limits that the implementation must respect

The detailed audit, rechecked at the current source pin, found the typed producer limited to exact compiler-owned raw storage, constant in-range indexing, narrow same-block projection patterns, and an eight-byte-field admission rule. Backend guards admitted the custom native x86-64/host lane; paired LLVM work rejected unsupported typed-storage evidence. These are concrete restrictions to remove deliberately, not flags to bypass. Implementation work must revalidate each gate at its starting revision. [R08]

The common layout heuristic can prefer SoA/AoSoA/Grouped based on static facts, but its selection is not an end-to-end conversion or an XRay-derived cost model. Intersect planned candidates with actually qualified producer, mapper, backend, host and target capabilities.

### 2.3 Specific collection behavior that migration must preserve

- Current adaptive lookups can update observations and change representation; they are not inherently immutable/shared-reader operations.
- `contains_key` must distinguish a missing key from a present optional/nil value.
- Preserve actual `entries`/`keys` ordering guarantees and fallback behavior. Do not assume an implementation called a hash map has unobservable iteration order.
- Native ordering support is more restricted than the generic `Ord` spelling suggests; aggregate-key admission needs real typed comparator support.
- All backing-container fields can exist in an adaptive instance, with extra ordering metadata where required. Do not budget as though only one allocation necessarily exists.
- Existing small-size/promotion thresholds are implementation defaults, not measured universal optima.

### 2.4 Corrected baseline claims

There is no need to invent adaptive sets/maps or AoS/SoA vocabulary from scratch. Conversely, the presence of these components does not establish universal layout switching, common attribute generation, or XRay-based planning. The target of this report is the **missing coherent integration and its evidence**, not a rename of existing source.

## 3. One logical schema and generated field access

### 3.1 What an attribute means

A managed attribute is a typed logical field identified by `(TreeSchemaId, AttrId)`. A proposed descriptor contains:

| Descriptor fact | Purpose |
|---|---|
| Canonical attribute name and semantic type | Name resolution and exact type checking |
| Applicable typed node views | Reject unsupported property access |
| Visibility and write authority | Preserve language and owner encapsulation |
| Required/default/optional contract | Whole-node construction validation |
| Phase and mutability policy | Frozen core, mutable owner state, or separate analysis result |
| Stored/forwarded/computed implementation | Generate the correct operation, not an untyped lookup |
| Semantic effect and borrow behavior | Check aliasing, reads/writes and callbacks |
| Declaration provenance | Source/config diagnostics, LSP and cache invalidation |

The physical plan separately records offsets, columns, occupancy/index representation and layout epoch. Changing a physical plan cannot change an attribute's meaning.

### 3.2 Type consistency

Within one tree schema, every resolved use of an attribute name has the same canonical type, including generic arguments and relevant qualifiers. Aliases are resolved; distinct nominal types are not collapsed just because both wrap `u64`.

| Declaration combination | Decision |
|---|---|
| SPL and SDN both declare `source_span: SourceSpan` | Merge matching declarations and retain both provenances |
| One declares `source_span: text` | Error with both locations |
| Two node views declare `left: ExprRef` | Valid; view-specific constraints may differ |
| Another view declares `left: SymbolId` | Error in the same schema; use a different canonical name or schema |
| Optional versus required declaration for the same property | Conflict unless a precise, explicit schema rule reconciles applicability; never last-writer-wins |
| Sparse physical storage for a required applicable field | Allowed only when finalization still proves a value/default for every applicable ready node |

Use exact canonical identity to resolve collisions; a short hash or interned integer alone is not a global type proof. Strong typed `AttrKey<Schema,T>` handles should be available to generic code without exposing `Any`.

### 3.3 Source declaration and generated view

Proposed syntax using existing annotation/class/field punctuation, not inheritance:

```simple
# Proposed node/attribute annotations; not claimed implemented.
@node_tree("compiler.ast")
class BinaryNode:
    source_span: SourceSpan
    left: ExprRef
    right: ExprRef
    operator: BinaryOp
```

The class describes a logical typed view. The generator emits its storage binding, builders, validators, borrow/projection metadata, and property operations. The view may contain a compact qualified handle rather than all payload fields. Common properties can be declared once in schema configuration or reused through the existing composition/trait/forwarding mechanisms.

`@node_tree` is an explicit opt-in storage/type contract. It does not authorize rewriting arbitrary ordinary classes or value structs into identity handles; their existing copy/move semantics remain unchanged outside this contract.

```simple
# Proposed API usage after finalization.
val span = node.source_span
node.left = replacement
```

Conceptual lowering:

```text
Resolve logical property -> check type/visibility/authority
    -> AttrRead or AttrWrite with original site identity
    -> static semantic advice, if admitted
    -> qualified storage projection or accessor
    -> optional observational profiling
```

The exact event placement for successful operations is specified in section 9. The final physical load/store can inline when eligible; "virtual attribute" does not imply a runtime virtual function call.

### 3.4 Addressable places, not just get-copy-set sugar

The lowering must distinguish a value from an assignable place. Required cases include:

| Source operation | Required behavior |
|---|---|
| `n.field` | One logical read; preserve copy/borrow semantics of the field type |
| `n.field = rhs` | Evaluate operands once in the language-defined order; one successful logical write |
| `n.count += delta` | One evaluated receiver, one read and one write, or a declared atomic RMW operation |
| `n.settings.mode = m` | Update the nested place; do not mutate a discarded temporary copy |
| `n.children[i] = child` | Preserve bounds, ownership and topology rules; do not accidentally replace the whole collection |
| Borrow of a field | Supply an admitted pinned/leased projection or reject; never return an address that migration can invalidate |
| Move-only field read | Enforce move/take rules; do not silently clone because storage is SoA |
| Volatile/MMIO/atomic property | Preserve exact access and ordering semantics; do not convert based only on profile preference |

The inspected Pure-Simple assignment path evaluates RHS before receiver. The project must establish the authoritative ordering and make all engines agree; this report does not silently impose a different order. Tests use side-effecting receiver/RHS expressions to expose duplication or reordering. [R04]

Computed properties explicitly declare effects, failure behavior and optional setter implementation. Storage-independent pure projections may participate in layout planning. Arbitrary effectful getters are not assumed equivalent to direct memory reads. Copy-out/copy-back is allowed only when its alias, exception/error, ownership and update semantics are proved equivalent.

### 3.5 Generated code and tools

Mark generated accessors as semantic artifacts carrying their schema/AttrId/origin, not removable dummy wrappers. Existing getter/setter cleanup tools must recognize this distinction. LSP should show the logical field, type, owner, physical policy, and generated target on demand; source navigation should return to the schema declaration rather than an unstable generated filename. [R17]

### 3.6 Accessor-generation matrix

| Logical declaration | Implicit generated operations | Aspect/observation surface |
|---|---|---|
| Mutable stored attribute | Typed getter, authority-checked setter, construction initializer | Logical `get` and successful `set`; separate initialization events |
| Read-only stored attribute | Getter and construction initializer; no public setter | `get`; owner initialization is not a fake later write |
| Getter-only computed attribute | Checked getter bound to declared implementation/dependencies; no fabricated storage | One logical `get` with declared effects/failure behavior |
| Forwarded property | Getter and, only when explicitly allowed, checked setter through the target | Outer logical property is the selected surface; implementation observation is separate |
| Later-phase analysis result | Typed result/sidecar access with phase readiness | Result-ready/access events, not an uninitialized core-node field |
| Equivalent SDN declaration | Exactly the same typed surface as its SPL equivalent | Same canonical selectors/site semantics regardless of declaration origin |

Generation also produces schema descriptors, requiredness validators, stable field identities and storage projections. It does not automatically generate setters for every getter or allow external code to mutate owner-private state.

## 4. Whole-node initialization and removal

### 4.1 `NotInit<Node>` is an initialization obligation

`NotInit<T>` is proposed as a must-resolve construction handle: initialize and finish, or explicitly discard. Ordinary affine ownership alone permits dropping and is therefore insufficient; a separate initialization obligation must be enforced. This is not merely another spelling of `Option<T>` and not raw uninitialized memory exposed to user code.

| State/type | Meaning | Allowed operations |
|---|---|---|
| `NotInit<BinaryNode>` | Reserved construction, not a usable binary node | Assign required fields through initializer operations, finish, discard |
| `BinaryNode` / ready typed handle | Valid, fully initialized node for its declared phase | Normal admitted reads and writes |
| `Option<BinaryNode>` | Intentional absence or a ready node | Ordinary optional handling |
| Retired/stale handle | Node removed, region expired, or slot generation changed | Explicit failure; never silently read a reused slot |

A `None`-like internal sentinel may represent the pending state; it must not permit an implicit conversion to a ready node. An applicable property that is itself optional remains `Option<T>`, not `NotInit<T>`.

### 4.2 Construction protocol

Illustrative API contract:

```text
create<T>(region) -> Result<NotInit<T>, AllocationError>
initialize(pending.field, value) -> checked initializer operation
finish(pending) -> Ready<T> on success; retains the pending obligation on failure
discard(pending, reason) -> consumes obligation and reclaims reserved resources
```

Surface example, with failure handling abbreviated rather than hidden:

```simple
# Proposed API. These assignments are initializer writes, not reads of T.
var pending: NotInit<BinaryNode> = tree.create<BinaryNode>()?
pending.source_span = span
pending.left = left
pending.right = right
pending.operator = BinaryOp.Add
val node = pending.finish()?   # actual API must preserve/clean up on failure
```

The final API must make the failure branch sound. Either an error retains the builder for correction/discard, or a consuming fallible finalizer performs explicit rollback. A normal `?` path may not leak an unresolved builder. The generated builder uses an internal required-field bitmap or an equivalent statically proved state; it does not change every user field's type.

Defaults are declared and initialized exactly once. No implicit numeric-zero, empty-string, nil or invalid-ID default is invented for missing required fields. Static definite-initialization proves simple cases; runtime checks cover dynamic construction. A ready-node read does not repeat a whole-node field scan.

For the first version, reject a second initializer write to an already initialized slot. During finish, apply declared defaults only to still-unset fields; do not eagerly fill defaults and then misdiagnose an explicit initializer as a duplicate. On a retry after partial default evaluation, retain the initialized-state bookkeeping so defaults do not execute twice. Never overwrite an owned value as if the slot were empty. Any later explicit builder-replacement operation must release the previous value exactly once and define failure behavior.

Only stored initializer-writable fields carry assignment obligations. A getter-only computed/forwarded property needs ready declared dependencies or a ready forwarding target, not a dummy field or fabricated initializer write. An effectful computed getter's possible failure belongs to its access contract; it is not itself evidence of an incompletely initialized node.

### 4.3 Dropping, cancellation, and removal

- Dropping a still-pending builder on an ordinary path is a compile-time error when known, with a checked runtime diagnostic otherwise. A migration-only warning mode must be explicit and temporary.
- `discard` means "this node is intentionally not needed"; it is not an unsafe `assume_initialized` operation.
- Region abort/cancellation provides an explicit cleanup path that consumes all pending obligations and releases initialized owned members exactly once.
- Removing a ready node requires owner mutation authority, validates incoming edges according to topology policy, retires the slot, and invalidates aliases through generation/region checks.
- Reusing a variable may assign a new `NotInit<T>` to that variable; it does not rewrite every copied alias to an old node.
- Generation exhaustion retires the slot/region or follows a verified wider-identity policy. Never wrap silently and revalidate stale handles.

### 4.4 Phases and cycles

An AST can be ready without a future inferred type. Put later analysis results in a separate typed HIR/analysis view or a versioned write-once result sidecar. Do not publish an "initialized" AST whose advertised required field remains uninitialized until some later pass.

Use the existing async resource/result mechanisms for not-yet-produced analysis results; do not add a future to every property. Cache a whole result or appropriate result group under its exact semantic key.

Strict trees reject structural cycles and enforce child-order/parent rules. A graph/SCC mode can reserve several pending IDs, assign internal edges, and atomically finalize the whole construction group after completeness and topology validation. Pending IDs must not escape as dereferenceable ready nodes. Build dependency DAGs retain explicit cycle detection; this feature must not reinterpret them as unrestricted graphs.

## 5. Node identity, regions, and topology

### 5.1 Separate identities

| Identity | Meaning | Must not be confused with |
|---|---|---|
| `RegionId` | One allocation/ownership domain within a qualified session/namespace | Borrow-checker region, trace timing region, RDMA registration, recovery group |
| `ObjId` | One managed object/container within its documented identity domain | Hash value, raw address, artifact content digest |
| `NodeId` | A node slot/entry inside the appropriate object/pool | Physical array offset or hash bucket after reorganization |
| Region generation | Detect retirement/recreation of an ownership domain | Node-slot reuse or representation change |
| Node generation | Detect removal/reuse inside its qualified store and region generation | Physical representation epoch |
| Representation epoch | Which layout/index root a view resolves through | Semantic node identity |
| `ArtifactId` / snapshot identity | Immutable serialized value or compilation stage | Session-local runtime ID |
| `RunId`, task/action, attempt | Build invocation, semantic action and execution attempt | Node lifetime or profile session |

A conceptual qualified reference is `(namespace, RegionId, region_generation, ObjId, NodeId, node_generation)`. This plan uses `ObjId` for the store/container and `NodeId` for its typed local node slot, not a second globally allocated object identity. A one-node object may omit the extra local locator. Do not reuse `ObjId` within a live region generation; an implementation allowing reuse must add an object generation or prove an equivalent fresh composite incarnation.

Implementations may compress fields when an enclosing lease/view already supplies them. Do not put a full global tuple on every edge when a checked region-local index suffices. Compact IDs remain local; serialization restores their required context.

Changing AoS to SoA or rebuilding a map does not by itself change logical node identities or slot incarnations. It changes the physical root/epoch. Deletion/reuse does change the lifetime identity. Hash indexes map stable entries to locations; buckets are never public identity.

### 5.2 No tag field, but valid type identity

Homogeneous storage can encode the node type in `NodeView<T>` and its pool descriptor. A heterogeneous store uses a pool/class/schema descriptor or checked internal discriminator. The public API does not require `node.tag` or a manually maintained `kind` field.

Do not remove existing internal `expr_tag` data before all parser/lowering/codec consumers have an equivalent verified type identity. A typed view is not permission to cast one node class into another without checking pool/schema membership.

### 5.3 Topology storage

Provide a small set of explicit topology contracts: ordered tree, DAG, and general graph only where requested. Initially retain existing adjacency representations behind generated accessors. Later candidates can include contiguous child slices for frozen trees, per-node arrays for mutable child lists, and chunked adjacency for high-churn regions.

Topology changes are semantic mutations; physical reordering is not. A packing pass may reorder slots while retaining node IDs and child order. It may not sort semantically ordered children or remove repeated edges merely to make a faster lookup.

### 5.4 Ownership and transfer

Reuse `TransferEnvelopeV1` and existing owner-result messaging. A process worker receives encoded immutable inputs or an admitted shared handle, never an in-memory view/vtable/pointer. Region ID plus object ID is necessary context, not sufficient authorization: generation, owner/attempt fencing and payload validation still apply. [R16]

Memory residency pins and view leases are not the forbidden exclusive compile-path process leases from the cache plan. Their purpose is to prevent reclamation while data is in use; they must not serialize unrelated compilation producers.

## 6. AoS, SoA, and related layouts

### 6.1 Reuse the canonical layout contract

Keep `StorageLayoutKind`, `StorageConversionPolicy`, and `StorageLayoutPlanV1` as the physical-layout vocabulary. Add profile/capability input through a versioned adapter or companion plan, not by silently changing frozen V1 field meanings. Preserve the separate raise-only memory/safety policy: it can disallow a layout but is not another layout selector. [R06], [R07]

| Layout | Often useful when | Principal limitations |
|---|---|---|
| AoS | Operations consume most fields of one record; small objects; stable row ABI | Scanning a small field subset can load unrelated data |
| SoA | Bulk operations repeatedly read selected fields; contiguous column access | Whole-row access spans columns; row pointers are generally not available |
| AoSoA | Qualified vector/block processing benefits from grouped lanes | Block width, tails, padding and backend lowering must agree |
| Hot/cold or grouped | A stable hot field subset dominates | Additional indirection and conversion; not universally implemented |
| ExternalFixed / pinned | FFI, wire/MMIO, externally observed addresses/layout | Automatic representation replacement is disallowed |

These are workload hypotheses, not measured speedups for Simple. Layout is chosen for the actual operation mix, target and ownership contract. Avoid hard-coding “SoA is always faster.”

### 6.2 Storage-backed attributes bridge row and column access

A logical `AttrRead(qualified_handle, AttrKey)` first validates schema/pool membership, region and node generations, authority and the relevant lease. It then resolves stable node identity to a physical ordinal and lowers to the admitted mapping. AoS uses a row stride and field offset; SoA uses a column base and element stride; an admitted sparse attribute first resolves presence/index. Keep this projection visible in HIR/MIR until ownership, bounds, effects and aspect selection have been resolved.

For a field-by-field scan, generate column-oriented iteration rather than repeatedly reconstructing a full temporary node/record. For a whole-record operation, use a typed view or explicit materialization with counted copy cost. Do not promise a contiguous `T*` from a SoA collection.

### 6.3 Scope of automatic conversion

Automatic conversion initially applies only to opaque, compiler-owned storage with proven bounds, no escaping physical address, admitted element move/drop behavior and a qualified backend. Ordinary RuntimeValue arrays are not reclassified as raw typed storage just by attaching a layout label.

Reject or retain the original representation when any required fact is unknown:

- FFI, volatile/MMIO, fixed address, explicit layout or address observation.
- Outstanding iterator/borrow/pin incompatible with conversion.
- Mixed ownership, custom move/drop behavior, or partial initialization without an admitted conversion recipe.
- Unsupported field width/alignment, target ISA, endian mapping or layout kind.
- Peak-memory budget or progress contract cannot be satisfied.

SoA does not imply disjoint mutable borrows; two views can still alias the same column. Layout must never manufacture `noalias`, `nonnull`, alignment or bounds facts without proof.

## 7. Set and map algorithms

### 7.1 Preserve semantic families

The user-facing set remains exact membership with uniqueness; a map remains exact key/value lookup; a sequence retains order and duplicates. A sequence may gain a secondary membership index without changing into a set.

Use the existing `auto`, `linear`, `hash`, and `ordered` vocabulary for current adaptive containers. In a proposed SDN compatibility alias, `array` may normalize to **linear entry-array storage**. It must not mean a direct-index array unless dense bounded integer keys are explicitly proved.

Represent a plan with separate `algorithm`, `implementation`, `layout`, `hash_function_policy`, and `ordering` facts. “Hash” does not identify a hash-table algorithm, and selecting XXH3 versus a keyed hash is different from selecting chaining versus open addressing.

### 7.2 Candidate inventory

Complexity below describes standard algorithm families, not measured Simple performance or universal worst-case guarantees. `n` is live entries; bounds assume the required comparator/hash contracts.

| Candidate | Lookup / update characteristics | Eligibility and use | Adoption status |
|---|---|---|---|
| Linear entry array | Lookup O(n); compact iteration; update can scan | Small collections, few lookups, locality | Existing adaptive backend |
| Sorted entry array | Lookup O(log n); insertion/removal generally O(n) movement | Read-mostly or frozen maps, ordered traversal | Candidate; qualify adapter and semantics |
| Separate-chaining hash | Expected O(1); worst-case O(n) | General hashable keys, accounted allocations | Current generic hash foundation |
| AVL ordered map | O(log n) comparison/tree work; allocation, array growth and movement need separate bounds | Ordered/range behavior or collision-resistant comparison bounds | Existing ordered backend; key-representation limits remain |
| Robin-Hood open addressing | Expected short probes; movement on insert/erase/rehash | Movable entries, no address-stability promise | Future candidate, benchmark before promotion |
| Swiss-style grouped probing | Group metadata can accelerate candidate scans | Qualified SIMD/scalar implementation and erase/load policy | Future candidate; not the current hash backend |
| Bucketized cuckoo hashing | Bounded candidate bucket probes; relocation/rebuild costs | Workload-specific read-heavy use; qualified concurrency policy | Later optional candidate, not automatically lock-free |
| B-tree | Logarithmic ordered search, multi-entry nodes | Ordered/range scans and locality | Future admitted alternative, not synonymous with current `ordered` |
| Dense direct index | O(1) by bounded integer key; memory proportional to domain | Proven compact domain and explicit holes/presence | Specialized candidate |
| Bitset / chunked bitmap | Fast integer-set membership/set operations | Set-only bounded integer semantics; memory/domain proof | Specialized candidate |
| Frozen perfect-hash index | Construction cost; constant-time candidate lookup | Fixed key set and exact membership verification for nonmembers | Later immutable-only candidate |

Do not implement all candidates before shipping the common contract. Start with the three real adaptive backends, then add sorted arrays and one measured hash alternative. Candidate registries must describe semantic guarantees, allocator/drop behavior, target support, migration recipe, concurrency/progress and measured cost provenance.

### 7.3 Hard constraints precede cost

Before considering a representation, require:

1. Exact equality/hash/order consistency, including duplicate keys and optional values.
2. Preservation of observable iteration and update behavior.
3. Required key traits actually callable on that backend, not merely present in a generic bound.
4. Compatible reference/iterator invalidation and ownership rules.
5. Admitted memory bounds, target implementation and progress policy.
6. No unaccounted side effects from changing how often equality/hash/comparison executes.

Public concrete layouts and exported bucket fields cannot be rewritten as if they were opaque storage. Introduce an explicit opaque/representation-neutral facade and a migration period where necessary.

Abseil's container documentation is a useful warning: different container families have materially different pointer and iterator stability. That is a semantic eligibility issue, not merely a performance trade-off. [E03]

### 7.4 Current live switching versus future shared migration

Retain existing exclusively owned `AdaptiveMap` promotions/demotions behind the common policy adapter. Preserve its ordering/nil handling and test all directed transitions. For node getters and frozen compiler snapshots, use a read-only lookup adapter: an ordinary property read must not secretly trigger an unsafe shared-storage migration.

For the 3,000-key / 3,000-simultaneous-request cache objective, select only implementations admitted by that cache's strict progress and ownership contract. Neither the current mutable adaptive map, a fine-grained-lock cuckoo implementation, nor the active global-lock profile recorder qualifies as lock-free merely because it uses atomics somewhere. If no alternative qualifies, retain the admitted original and report the rejection reason. [D04]

## 8. Unified source and SDN configuration

### 8.1 One resolver, several independent policy dimensions

Introduce a proposed **data-policy envelope** that composes, rather than replaces, existing owners:

| Policy dimension | Existing/proposed owner | Example decision |
|---|---|---|
| Logical schema | Proposed shared attribute/schema resolver | `left` has type `ExprRef`; required on `BinaryNode` |
| Safety, ABI, progress | Existing memory/ownership policies plus explicit constraints | No address-observed conversion; strict cache progress |
| Layout | Existing `StorageLayoutPlanV1` | SoA with checked alignment |
| Lookup representation | Existing CollectionPlan/adaptive policy plus implementation registry | `hash` using the current chained implementation |
| Occupancy/topology | Proposed node-storage plan | Sparse diagnostic column; ordered child slices |
| Observation | Planned shared trace facade [D05], composed with the existing capture/profile owner | Sample attribute use and map probes via XRay provider |
| Application | Proposed explicit application policy | Rebuild, next instance, or admitted safe-point migration |

The envelope records exact referenced schemas and digests. It is not a second compiler planner with independent truth.

### 8.2 Source declarations and hints

Current implementation has `@collection_algorithm("auto"|"linear"|"hash"|"ordered")` for admitted adaptive constructors. The following additional spelling is a proposal reusing existing annotation punctuation; generic layout and node annotations require implementation and parser/semantic tests:

```simple
@collection_algorithm("auto")
var symbols = AdaptiveMap<SymbolId, Binding>.new()

# Proposed annotations, not existing universal array support.
@data_policy("compiler_nodes")
@layout("auto")
@node_tree("compiler.ast")
class BinaryNode:
    source_span: SourceSpan
    left: ExprRef
    right: ExprRef
    operator: BinaryOp
```

Use simple scalar annotation arguments first. Do not rely on the earlier illustrative named-argument syntax being supported across every parser. Local annotations must survive parsing, macro expansion and lowering with stable creation-site provenance. No new reserved keyword is needed; accepting an annotation name is not proof that its semantic meaning is implemented.

### 8.3 Configuration can declare or extend the schema

An explicit build input can declare a complete node schema or additional allowed attributes. It must resolve imported type names and owner visibility before generating declarations. It cannot silently change an existing attribute's type, requiredness, default, ownership or effects.

Illustrative SDN structure; **these keys define the proposed schema, not an already implemented build configuration**:

```sdn
data_policy:
    schema: "simple.data-policy/v1"
    default_application: "next_build"
    declarations:
        binary_node:
            tree: "compiler.ast"
            view: "compiler.ast.BinaryNode"
            attributes:
                source_span:
                    type: "compiler.SourceSpan"
                    required: true
                left:
                    type: "compiler.ast.ExprRef"
                    required: true
                right:
                    type: "compiler.ast.ExprRef"
                    required: true
                operator:
                    type: "compiler.ast.BinaryOp"
                    required: true
    rules:
        compiler_nodes:
            selector: "compiler.ast.*"
            layout: "auto"
            occupancy: "per_attribute"
            application: "next_build"
            profile_group: "compiler_data"
        symbol_map:
            site: "compiler.resolve.symbols"
            algorithm: "auto"
            implementations: ["linear", "chained_hash", "avl"]
            application: "next_instance"
            profile_group: "compiler_data"
        sparse_diagnostics:
            attribute: "compiler.analysis.diagnostic"
            lookup: "hash"
            occupancy: "sparse"
            application: "new_snapshot"
    profiles:
        compiler_data:
            provider: "trace"
            events: ["data_field", "collection", "node_traversal"]
            sampling: "bounded"
            raw_values: false
            on_loss: "mark_incomplete"
    trace:
        backend: "auto"
        instrumentation: "dynamic"
        consistency: "raw_edges"
```

Schema-declared fields in this example may instead be declared in SPL. Identical dual declarations are reconciled; conflicting ones are errors. The selector `compiler.ast.*` is resolved to canonical owners/sites, not searched as a string in the hot path. A configuration-only declaration must have an explicit module/build owner and a generated-surface manifest; it cannot inject fields into an arbitrary external package without authority.

The trace backend is a **build/config choice**, not hard-coded in data classes. Runtime selectors may enable prepared observers; they cannot manufacture missing instrumentation or change an admitted ABI profile.

### 8.4 Conflict and precedence rules

There is no universal “config always wins” rule.

| Input kind | Resolution rule |
|---|---|
| Type/semantic schema declarations | Exact agreement or diagnostic; no silent override |
| ABI, ownership, safety and critical progress constraints | Hard intersection; a profile can never weaken them |
| Explicit source physical pin | Binding unless explicitly declared externally overridable |
| Explicit build physical pin | Applies only within the owner's allowed choices; conflict with a source pin is an error |
| Source/default performance hint | May be refined by a more specific permitted build rule |
| Admitted profile preference | Ranks remaining `auto` candidates only |
| Compiler default | Deterministic, versioned fallback when evidence is absent |

For build rules, use deterministic specificity: exact declaration/site, exact owning type, module/directory rule, then project default. Conflicting equal-specificity rules are errors, not file-order accidents. Command-line options are explicit policy inputs, not an undocumented bypass of hard constraints.

Resolve per compilation/run context; remove dependence on an ambient process-global profile catalog where simultaneous builds need distinct policies. Freeze the resolved plan before workers receive it. LSP, compiler, interpreter, BuildRunner and `explain` must read the same resolved result.

### 8.5 Canonical identity and explainability

Record separately:

- `SchemaDigest`: types, applicability, required/default semantics, visibility and effects.
- `PhysicalPlanDigest`: concrete layout/index/occupancy/topology implementation and version.
- `InstrumentationPlanDigest`: selected logical sites, event schema, provider ABI and instrumentation mode.
- `ProfileArtifactDigest`: exact admitted capture and decoding metadata.
- `ResolvedPolicyDigest`: constraints, provenance, application mode and planner version.

Normalize logically equivalent configuration before digesting; path aliases and key order must not create unnecessary differences. Preserve exact input/provenance receipts without treating every incidental file byte as a new semantic type. Every decision reports selected representation, rejected candidates, eligibility facts, cost evidence, profile coverage and the next legal application point.

## 9. Aspects and logical get/set events

### 9.1 One semantic access path

Introduce canonical `AttrRead`, `AttrWrite`, initializer-write, and optional declared RMW metadata before physical lowering. Adapt existing AOP models to this contract rather than adding a third unrelated matcher.

Generated accessors and direct physical fields share logical field identity, but not necessarily identical implementation. A read through `node.left` and its generated internal call describe **one** logical read. Raw map/array accesses performed by that implementation are not additional user property events.

Generated accessor helpers are excluded from ordinary `execution(...)`/`call(...)` matching by default. Explicit helper tracing, if offered, is a separate opt-in implementation-level observation domain. One source field access must not accidentally trigger logical get/set advice, generated-function advice and backing-map advice as three observations of the same property operation.

AspectJ's field get/set join points and MLIR's generated typed accessors are useful precedents for separating logical operations from implementation details. They do not imply those capabilities already exist in Simple. [E04], [E05]

### 9.2 Field selectors and existing annotation selectors

Do not conflate `attr(...)`'s declared meaning—selection by declaration annotation metadata—with a data attribute read/write. The validator accepts `attr(...)`, but the inspected tokenized compiler and interpreter matchers currently evaluate it as false; this is not end-to-end annotation-pointcut support. The proposed field selectors are `get(...)` and `set(...)`, resolved against canonical field symbols and owning views. [R14]

Keep the existing pointcut Boolean vocabulary (`&`, `|`, `!`) and token-aware parser. `get(...)`, `get (...)`, multiline spacing and malformed parentheses must receive equivalent validation. The current immediate-parenthesis extractor cannot remain the authority for a newly enabled feature. [R14]

Enable selectors only when parsing, type resolution, matching, lowering, interpreter behavior, error reporting and tests support the selected lane. Unsupported forms remain explicit errors. A parser accepting a selector that never matches is not support.

### 9.3 Successful operation semantics

| Operation | Logical observation contract |
|---|---|
| Field read | One completed-read observation after a valid read; optional separate attempted/failure record |
| Field write | One completed-write observation after a committed valid write |
| Initializer write | Distinct construction observation; never fetch an old uninitialized value |
| Compound assignment | One read plus one successful write, or one explicitly declared atomic RMW record; choose and version the contract |
| Node finish/discard/remove | Lifecycle events, not an inferred sequence of ordinary field writes |
| Representation conversion | A migration event plus aggregate counts; not replay of every user's setter/advice |
| Static field eliminated or folded | Instrumentation mode explains coverage; do not claim an optimized physical trace is a complete source-read count |

Evaluate receiver, index and RHS exactly once and preserve the authoritative language ordering. Do not log a successful setter before storage validation or before a fallible update commits.

### 9.4 Semantic aspects versus optional observers

Hard initialization, bounds, type, ownership, visibility, atomicity and scheduler-state invariants are part of normal generated access semantics. They cannot depend on whether a profiling aspect is loaded or XRay is enabled.

Keep optional data profiling observational. V1 language advice can retain the existing parameterless/unit-returning ABI; internal trace records carry checked numeric schema/site identities through the separate observation extension. This does not silently add general argument/return capture or dynamic `around`/value replacement.

An observational callback must not synchronously mutate the observed object, throw through a trampoline, allocate an unbounded structure, wait for a build task, or decide a migration. Exclude tracing/runtime infrastructure from recursive instrumentation and use a cleanup-safe per-execution-context guard. Aggregate failures/loss are reported; they must not turn an application operation into fictitious success.

Static semantics-changing advice, where separately supported, remains in the compiler's normal effect/error/ordering contract and cache identity. A disabled XRay observer does not disable that semantic advice. Schema introductions require an explicit introduction manifest before type checking and feed the effective directory/TLDR surface.

## 10. Shared XRay profiling architecture

### 10.1 Provider-neutral public interface

Follow the staged XRay plan's public lifecycle: capabilities, prepare, start, request_stop, drain, poll, flush, stats, release. Applications, NodeStore, adaptive collections and optimizer clients do not call `__xray_*` directly. [D05]

| Provider stage | Scope | Data-system contract |
|---|---|---|
| 1: Linux LLVM XRay | Qualified hosted LLVM/compiler-rt path | Common data event extension; backend-private site map adapter |
| 2: Linux Simple-owned tracing | Same public facade, Simple-owned emission/runtime | Same schemas and decisions; rebuild private instrumentation format as necessary |
| 3: Windows Simple-owned tracing | Independently qualified x64/ARM64 host/ABI leaves | Same public API; explicit capability/experimental status until qualified |

PR #5962 adds an experimental native Windows verification lane, not a production Simple provider. Its expanded CI run succeeded on Windows x64 and ARM64. These are pre-existing CI results inspected for this report, not tests executed during report preparation; the run tested the PR revision later included in the pinned merge. [R18]

| Current evidence | Established scope | Still not established |
|---|---|---|
| Native scalar sled integration | Fixed-ID scalar function; disabled/enabled entry and exit; 15,000 transitions under concurrent calls without wrong IDs/results | Arbitrary generated functions, typed fields, exact paired spans, compiler/LTO/maps |
| Separate x64 ABI regression | Reproduces baseline YMM-upper/MXCSR defects; bounded remedy preserves YMM0–15, MXCSR and tested flags with OS-enabled AVX | AVX-512/AMX/APX/x87/special ABIs; live patching of the bounded remedy |
| Separate mitigation executables | CFG on both targets; x64 CET compatibility-mode enforcement; ARM64 PAC enforcement | Strict CET, ARM64 BTI enforcement, recorded PAC-policy association with the scalar trampoline executable |
| ARM64 trampoline source | Explicit integer/SIMD/flags/FP saves and restores | Comprehensive native state-snapshot qualification |

The concurrent integration harness temporarily uses executable-writable pages; it does not qualify a strict W^X production patch protocol. Entry and exit are independently switched and concurrent totals differ: raw-edge success is not exact paired-span correctness. The bounded ABI regression and scalar patching test are separate tests. The original x64 trampoline remains a regression baseline, not an admitted universal production default.

Do not add Linux runtime dependencies to Windows builds during earlier stages, and do not change the freestanding SimpleOS builtins-only configuration incidentally. Resident code/maps avoid a new hot-unload requirement; session-generation, admission, quiescence and drain correctness still require qualification.

Function tracing, typed data events, live patching, and exact paired spans are separate capabilities. `Unsupported` must name the missing capability. Existing indirect joinpoint-slot dispatch must not be relabeled as XRay or silently substituted when an XRay provider is explicitly requested.

### 10.2 What XRay supplies and what must be added

LLVM documents patchable function instrumentation, selected-function activation, and custom/typed event facilities. Instrumentation is compiled into the executable; it cannot be enabled in a binary that lacks the required sites. [E01]

Function entry/exit records alone do **not** identify field co-access, key cardinality, hash collisions, attribute occupancy, tree traversal or physical relocation. Simple must generate explicit logical data observations or aggregate counter sites and connect them to the common facade.

Prefer:

1. Typed HIR/MIR access and collection-operation sites with stable logical identities.
2. Compact checked IDs in the hot path and cold schema/source maps.
3. Bounded per-thread/worker counters, sampled events, and aggregate snapshots.
4. XRay-capable custom/typed event emission where the provider is qualified; selected instrumented helper boundaries only where their extra call/noinline cost is acceptable and measured.
5. Existing `.sprof` validation, merging and file ownership, with a versioned data-record extension.

Do not force every tiny getter to remain uninlined merely to make it visible as a function. If boundary preservation is necessary for a selected profiling mode, measure its perturbation separately and exclude it from statically-off production builds.

### 10.3 Shared event and profile identity

Reuse the tracing facade's canonical header and reserve/declare the data-observation extension before freezing its deployed schema. If the base format is already frozen, use its advertised extension mechanism or an explicit negotiated new version; never reinterpret an old event ordinal.

Cold capture manifest:

```text
CaptureManifest:
  schema/version, source snapshot, executable/module digest
  provider + private instrumentation ABI + module instance map
  logical site map, tree/schema/type map, physical-plan map
  execution host and target identities, compiler/planner versions
  policy digest, workload ID, capture window and clock description
  sampling plan, loss/coverage indicators, bounds and provenance
```

Hot records use compact indices into this manifest: session generation, logical execution context, site ID, event kind, representation epoch and necessary region/object/attribute indices. Optional node IDs are sampled or aggregated; do not create a persistent record per node access by default. Never use a pointer as a durable object ID.

LLVM function IDs belong to a particular binary/map. They are not stable `AttrId` or logical creation-site identities. A map/digest mismatch rejects the profile, rather than assigning measurements to the wrong field.

### 10.4 Required measurements for the three families

| Family | Low-cost baseline observations | Optional deeper observations | Decisions they inform |
|---|---|---|---|
| AoS/SoA records | Field read/write counts, selected field groups, element-count bands, row/column materialization | Sampled co-access windows, stride/locality, hardware cache/memory counters from a separately identified provider | Layout, hot/cold grouping, block width, copy avoidance |
| Sets/maps | Size distribution, lookup/insert/remove counts, hits/misses, comparisons, probes, collisions, iteration | Key-size bands, bounded hash skew summaries, resize/migration durations and bytes | Linear/hash/ordered choice, implementation and capacity policy |
| Node trees/graphs | Live nodes by typed pool, attr occupancy, edge count/degree, traversal kinds, creation/removal, region lifetime | Sampled subtree locality, attr co-access, dirty-subtree/change rates, stale-handle diagnostics | Dense/sparse columns, row/column groups, adjacency packing, region granularity |

Definitions matter: a hash collision is not every probe; a successful lookup is not every getter; observed maximum is not a proved bound; CPU samples are not operation counts. The metric schema includes units, aggregation, sampling denominator, population and unknown states.

### 10.5 Avoid misleading profiles

- Keep zero distinct from not measured, unsupported, overflowed and dropped.
- Do not average percentiles from different runs and call that a merged percentile; merge compatible histograms/sketches or retain separate populations.
- Track warmup, phase, target, backend, representation and workload. A tiny cold set and a large warm set must not collapse into one unexplained average.
- Interpreter timing is not native timing. Counts/field-use patterns may transfer as explicitly qualified hints; native performance ranking requires target-appropriate evidence.
- CPU cache misses require an appropriate counter/sampling source; XRay timing does not magically provide them.
- A sampled absence never proves immutability, unused fields, unique ownership or bounded cardinality.
- Do not record raw keys, source text, values or absolute pointers by default. Opt-in diagnostic payloads require explicit bounds and ownership-safe copying.

### 10.6 Node-tree profiling is not the XRay call tree

A call tree describes execution nesting. A node tree describes application data topology. Link them through operation/pass/site and region/object identities; never infer one from the other.

For example, a `resolve_names` span can reference a compiler region and aggregate traversed node count, touched attributes, child visits and symbol-map operations. A later report can identify "this pass repeatedly scans two columns of this node family" without tracing every edge or storing the whole AST in the profile.

Include node creation/finish/discard/remove and representation-transition events. Pending nodes are not counted as ready; a failed pass does not become a valid finished-tree profile merely because its process exited.

### 10.7 Activation, overhead and lifetime

Keep three states distinct:

| Mode | Expected instrumentation behavior | Qualification |
|---|---|---|
| Static off | No data instrumentation dependency/site payload by construction | Inspect emitted artifacts and compare size/throughput |
| Prepared but disabled | Patch sites, maps and possibly retained boundaries remain | Measure code-size and inactive-path cost; not advertised as zero overhead |
| Active | Bounded recording/aggregation at selected sites | Measure throughput/latency/RSS and disclose loss |

Prepare maps, TLS/worker buffers and dispatch metadata before enabling callbacks. One resident provider/dispatcher owns registration; packs do not overwrite process-global handlers independently. Maintain subscriber ownership where observers share sites. Failed or partially patched selections are reported as such.

Disabling closes record admission; drain accounts for admitted events and loss. Preserve code/maps/providers until process exit according to the staged plan. Session release is not hot unload. Raw-edge sessions tolerate marked transition gaps; exact paired durations require the stronger paired-span capability. [D05], [E02]

The existing process-scoped capture recorder should be adapted, not copied into a second telemetry system. For strict cache hot paths, replace active global-lock/string work with bounded numeric per-worker aggregation or an explicitly qualified alternative. A nonblocking loss policy is acceptable only when the report records the loss and no correctness decision depends on complete samples.

### 10.8 Inlining, optimization and backend parity

Assign logical site identities before lowering and bind surviving machine sites after optimization/linking. Test LTO, inlining, cloning, constant folding, tail calls, early returns and unsupported paths. Do not claim to recover optimized-away field operations by a post-link function patch alone.

Offer an exact logical-access diagnostic mode and a lower-overhead optimization-oriented mode with explicit coverage/aggregation semantics. They answer different questions. Vectorized bulk operations may emit a batch record with a documented logical-operation count; they must not be mislabeled as one scalar read.

The current custom-native typed-storage lane and a future LLVM-XRay lane are separate capabilities. Existing support for one does not prove their combination. The first integrated pilot must exercise a producer/backend/provider combination that actually implements both, or report counts from a managed reference layout without claiming native physical conversion.

## 11. Profile selection and safe switching

### 11.1 Application modes

| Mode | What changes | Initial use |
|---|---|---|
| Report only | Nothing; explain eligible choices and evidence | First rollout and unknown workloads |
| Next build | A frozen plan is compiled into new artifacts | Default for compiler-owned layouts and compiled collection specialization |
| Next instance | Future instances use the new plan; existing instances retain theirs | Adaptive containers and newly created regions |
| New snapshot | Publish a separately built immutable result | AST/HIR/cache artifacts and frozen node trees |
| Exclusive live switch | Rebuild one exclusively owned instance | Existing adaptive-container model, after its ordinary eligibility checks |
| Shared safe-point migration | Publish a new root while controlling leases/readers | Later, independently qualified node/layout capability |

`next_build` changes the next output artifact, not the implementation of the currently running compiler. A compiler self-optimization experiment must build that compiler, then run the resulting binary on the comparison workload. Backend switching also normally requires rebuilding; it is not an implicit runtime migration of executable code.

### 11.2 Selection procedure

1. Resolve schema and semantic requirements independently of observations.
2. Enumerate implementations supported by the actual producer, backend, target and runtime.
3. Intersect memory, ABI, ordering, ownership, address, progress and migration constraints.
4. Admit profiles only after validating their identities, event versions, coverage and applicability.
5. Estimate candidate benefit including allocation, conversion, index maintenance, code size and expected remaining workload.
6. Retain the original when evidence is insufficient or improvement does not exceed uncertainty and transition cost.
7. Emit a frozen decision receipt and its earliest legal application mode.

An illustrative economic rule is:

```text
expected remaining work saved
    > conversion cost + added maintenance cost + uncertainty margin
```

Use compatible time/cost units. Cardinality, collision rate or one hot getter is an input, not the whole decision. A profile from linear storage cannot directly report the collision distribution of an unbuilt hash table; estimate it explicitly or measure a candidate in an offline/shadow experiment with accounted cost.

For live adaptation, require minimum observation windows, hysteresis, a cooldown, a maximum switch budget and a memory cap. Store these in versioned policy, not hidden global constants. Ignore early warmup when appropriate; record workload phase changes. Do not interpret the current 8/32-style collection defaults as measured universal thresholds. [R09], [R11]

### 11.3 Transactional representation migration

The following is the proposed general migration contract, not a claim that today's mutable adaptive containers implement concurrent snapshot publication:

| Stage | Required guarantee |
|---|---|
| Admit | Exact schema/current epoch match; recipe and target qualified; ownership permits migration |
| Quiesce or snapshot | Exclude incompatible writes/borrows, or use a separately proved concurrent protocol |
| Reserve | Budget old storage, new storage, indexes, buffers and delayed reclamation together |
| Build | Construct the new representation without changing the authoritative old root |
| Validate | Preserve all logical values, exact keys, ordering, topology, requiredness and identities |
| Publish | Atomically install one consistent root/plan/representation epoch at a defined linearization point |
| Retire | Retain the old root only for readers whose contract admits that snapshot; reclaim it after their leases end |

An OOM, invalid candidate, cancellation or validation failure before publication leaves the old representation authoritative. After publication, blindly restoring the old root could discard subsequent writes; rollback then requires a new validated transition from current state.

Preserve move/drop ownership. A copied pointer is not permission to destroy the same resource twice, and a move-only value cannot be moved out of the authoritative representation while unsynchronized readers still rely on it. Custom equality/hash/comparison callbacks require the semantic/effect constraints already described; a failed migration must not expose unintended user-visible callback effects.

For destructive move-only transfer, require a proved reversible recipe, or finish every fallible step first and then use an admitted infallible, non-cancellable transfer/publication phase. Cancellation is deferred through that phase under an explicit contract. Preallocation alone is not a rollback proof. If neither recipe satisfies ownership and progress/cancellation requirements, reject migration for that value type.

Never publish some node columns under the new layout while other columns or adjacency indexes still use the old epoch. A descriptor/root can reference an immutable set of mutually consistent structures. Slot generations remain lifetime identities; representation epochs track physical views.

Snapshot retention is not permission for a shared mutable handle to read stale values forever. Linearizable/current-state reads must resolve the appropriate current root, or use a separately proved versioned/forwarding protocol. A lease's consistency contract, not just its memory validity, determines whether reading an older root is allowed.

Raw pointers, FFI references, pinned address observations and mutable field borrows block migration unless an explicitly qualified protocol preserves them. A suspended task cannot carry an unchecked raw projection across an epoch change. A static proof may remove a runtime check, but a release build cannot remove the safety requirement.

Strict lock-free cache paths cannot acquire a global migration mutex as a silent fallback. Use an admitted protocol or restrict the policy to next-instance/new-snapshot operation. Epoch reclamation alone does not prove lock-free progress, bounded memory, or absence of stalled readers.

### 11.4 Controller versus observer

An XRay/data callback may update bounded counters or enqueue a bounded observation. The owner/controller later evaluates a proposal outside the callback. A proposal is revalidated against the current plan epoch and ownership state before use; an outdated profile recommendation cannot overwrite a newer owner decision.

Schema changes, new required fields and type changes are not representation migrations. They require a new schema/build/snapshot and any explicit semantic data conversion. Observers cannot introduce attributes into already compiled types.

## 12. Compiler, interpreter, and BuildRunner integration

### 12.1 Compiler pipeline

The proposed integration order is:

```text
SPL + SDN + explicit introduction manifests
  -> shared schema/config resolver and provenance
  -> typed logical properties, construction obligations and access places
  -> AttrRead/AttrWrite/init operations with original site identity
  -> effect/borrow/topology checks and static aspect composition
  -> eligible layout/collection selection and frozen decision receipt
  -> qualified MIR projection/accessor lowering
  -> backend instrumentation and final code/map validation
```

Property lookup and generated names must not collide ambiguously with existing real fields or user-defined getters. Preserve real-field behavior unless the declaration explicitly opts into managed-property semantics; reject conflicting managed definitions rather than letting source order choose. Existing `get_`/`is_` conventions need a compatibility adapter, not an independent second schema.

| Existing owner | Planned change |
|---|---|
| Frontend attribute/parser and `collection_feedback` [R11] | Preserve declarations/hints and canonical site origin; replace ambient catalog dependencies with explicit context |
| HIR field definitions and class lowering [R05] | Add schema/property/place and whole-node construction metadata |
| Semantic CollectionPlan selection [R12] | Consume admitted profile facts; preserve proof/memory gates and explicit rejection reasons |
| Storage analysis/producer/projection lowering [R08] | Connect eligible logical field operations; expand reads/writes, widths and control flow incrementally |
| AOP model and MIR injection [R14] | One logical get/set contract; no extra advice for implementation loads/stores |
| Backend helpers/native emission [R08] | Capability-gated layout plus instrumentation support; retain unsupported-lane rejection |
| Driver and app profile boundary [R11], [R13] | Freeze plan before workers; own profile loading/file I/O and artifact receipts |

Lower compiler/common layers must not import `app.optimize` merely to read a profile file. The app/driver loads and validates artifacts, then passes typed immutable facts into shared planning interfaces.

For bootstrap, first run the schema generator using the existing admitted compiler and check its deterministic output. Generated accessors must not require the very new feature needed to compile the generator. Stage the change through one pool and keep a reference implementation until self-host and native parity are established.

### 12.2 Interpreter parity

The Rust and Pure-Simple interpreters must consume the same resolved logical contract, even if their storage implementations differ. Audit both the visible access evaluator and the exported/active helper paths; updating only one duplicate evaluator is insufficient. [R04]

Required parity covers receiver/RHS evaluation order, visibility, exact type errors, missing attributes, initialization, stale handles, nested-place updates, move semantics, successful/failing aspects and event count. A missing property must not inherit an unrelated legacy zero-default behavior.

A managed reference AoS/SoA implementation can validate semantics in the interpreter; it is not proof of the same native ABI, SIMD behavior or speed. If an interpreter host cannot provide XRay, an explicitly selected counter/reference provider may still validate the observation contract, but the result must identify that provider and must not be labeled XRay-native evidence.

### 12.3 Compiler node-pool pilot

Start with an existing AST family and a small field set: a common source span, one child reference and a variant-specific scalar. Keep existing owner accessors as the storage boundary while generating a typed view over them. Do not expose private module arrays or inadvertently copy an owner array through a generated wrapper. [R02]

Use whole-node builders for newly constructed pilot nodes, qualified handles for reads and explicit owner mutation. Keep the existing internal discriminator until all consumers are migrated. Later extend to HIR/analysis sidecars and frozen cache snapshots.

Profile a real traversal and symbol-map workload, correlating pass/site with node region/object identities. Compare logical results with instrumentation off/on and every admitted representation. Only then broaden to other node families.

### 12.4 BuildRunner integration

BuildRunner's task graph is a dependency DAG, not automatically an ownership tree. Its parallel task/status/host arrays are candidates for a generated task view, but the scheduler remains the sole transition authority. [R15]

- Give each managed run/arena an appropriate qualified `RegionId`; assign `ObjId` to graph, task-table and result objects where identity is needed.
- Map semantic task/action IDs to managed handles without redefining action identity as an array index.
- Keep task/status writes owner-private. External `task.status = Succeeded` must not bypass process reaping, result receipts, output validation or attempt fencing.
- Carry schema/plan/snapshot/context identities in worker inputs. Validate returned region generation, action, attempt, context and artifact receipts before publication.
- Pass pointer-free encoded inputs or admitted shared mappings; never send a native node view or vtable address to another process.
- Profile enqueue/dequeue, dependency traversal, ready selection, result ingestion, allocation and data access separately from child-process wall time.

Use the existing scheduler, resources and result sharing. Do not add one scheduler or future per attribute, and do not reinterpret a physical memory pin as an exclusive compile-path producer lease. Where the current owner implementation uses mutexes or external serialization, that does not establish the strict cache progress profile required by the separate resource plan. [D03], [D04], [R15]

### 12.5 Profile domains and build modes

Keep **compiler execution**, **interpreted program**, **compiled application**, and **BuildRunner orchestration** as distinct profile domains. Host and target can differ. A compiler running on x86 does not produce measured ARM application timings simply by emitting ARM code. Correlate domains where useful, but do not sum nested inclusive spans and call the result exclusive CPU time.

| Build/runtime lane | Safe initial policy |
|---|---|
| Development/phase-3 diagnostics | Prepared selected tracing consistent with the earlier folder/aspect plan; data payloads remain bounded and explicitly selected |
| Release/phase-4 production | Static-off instrumentation by default; may consume an already admitted offline optimization plan |
| Release-like measurement build | Explicit separate instrumentation identity and overhead report; not silently substituted for production |
| Unsupported target/provider | Explicit capability diagnostic for a pin; `auto` retains an admitted original/default and explains why |

General backend support remains staged. The narrow custom-native x86-64 layout pilot, upstream hosted LLVM XRay functionality and the planned Simple adapter, managed interpreter counters and experimental Windows fixtures are separate evidence lanes. Require a combined test before advertising a combined feature. Freestanding SimpleOS and unqualified ABIs remain out of scope until explicitly added. [R08], [R18], [D05]

## 13. Cache, TLDR, reverse-reference, and persistence rules

### 13.1 Semantic versus physical cache identity

| Change | Required invalidation/identity behavior |
|---|---|
| Field type, applicability, required/default semantics, visibility or effects | Change schema and effective semantic surface; invalidate affected consumers |
| Private AoS/SoA or collection implementation change | Rebuild affected physical/code artifacts; preserve semantic reuse only if the public contract truly stays identical |
| Public ABI/layout or address behavior change | Semantic/ABI invalidation as well as object rebuild |
| Instrumentation sites/provider/event ABI change | Separate instrumented code/map identity; never reuse an incompatible map |
| New raw profile not consumed by planning | New evidence artifact, not automatically a new semantic program |
| Admitted profile changes selected plan or emitted specialization | Include consumed decision/plan identity in affected object/action keys |
| Runtime RegionId/ObjId allocation changes | Trace/runtime identity only; not incidental semantic cache churn |

Include the actual compiler/planner version, resolved policy, target/ABI and consumed inputs in reproducible action keys. Do not hide a profile-dependent decision behind an unchanged cache key. Conversely, a different capture timestamp should not invalidate semantic summaries when no selected fact or generated output changes.

Site identity must include its semantic owner and relevant generic/schema instantiation. Preserve the existing source-identity normalization rules until a versioned replacement is implemented; do not promise arbitrary edit tolerance from current parser ordinals/hashes. Short-hash collisions require exact disambiguation where correctness depends on identity. [R11]

### 13.2 Introductions, TLDR and reverse references

Generated fields and configured/aspect introductions are explicit semantic inputs. Their manifest feeds the effective module/directory surface and TLDR dependencies. A changed visibility or property effect cannot be hidden as a purely physical optimization.

Keep reverse-reference (`.rr`) incoming-user counts and projection maintenance separate from the public TLDR hash. The authoritative forward dependency manifests determine reverse projections. A partial/corrupt `.rr` state is unknown, not zero users; rebuild the affected authoritative projection or fail closed. Publish under the existing expected-root/fenced-writer contract. Do not create a second global invalidation database for data policies. [D03]

Snapshot publication and representation-root publication are related atomicity problems, not interchangeable transactions. A storage epoch must not be accepted as proof that an artifact/action receipt is current.

### 13.3 Persistent encoding

Keep `FileAstV1` and other existing codecs unchanged unless a versioned migration is explicitly implemented. In-memory SoA does not require a SoA disk format. A canonical pointer-free record encoding can reconstruct any admitted in-memory representation. [R03]

Encode logical IDs with their enclosing namespace/snapshot context; do not serialize process pointers, live leases or hash-bucket addresses. A directly mapped physical image additionally needs exact layout/version/alignment/endianness/bounds metadata and compatible readers. Hash seeds and randomized bucket placement are implementation details unless the format explicitly and safely captures them.

On decode, validate snapshot-local references and rebind them to fresh qualified runtime region/store/node identities. Loading an artifact twice creates independently valid runtime ownership; serialized generations or old ownership tokens cannot resurrect authority. Historical profile IDs remain attribution metadata, never dereferenceable runtime handles.

Extend existing `.sprof` ownership/versioning for data observations; do not invent a separate profiler store for each family. Bound all decoder counts/lengths and reject unsupported versions, corrupt identities and impossible metric relationships. Preserve checksums/content-verification requirements of the existing cache; a fast noncryptographic lookup hash is not a substitute for its integrity contract.

## 14. Implementation work packages

### 14.1 Ordered delivery

All work packages below are **planned**, not completed implementation. Existing components in section 2 are inputs to this work, not substitutes for its acceptance tests.

| Package | Scope and principal owners | Deliverable / exit gate | Depends on |
|---|---|---|---|
| W0 — Contract freeze | Shared schema, CollectionPlan, layout and trace owners | Versioned identity, property, policy, observation and capability contracts; existing V1 compatibility reviewed | This audit and current source recheck |
| W1 — One resolver | Frontend/common config, driver and LSP | SPL/SDN equivalence, conflict diagnostics, provenance and deterministic digests | W0 |
| W2 — Typed access and construction | HIR/semantics plus both interpreters | Access-place IR; generated operations; whole-node finish/discard; no public tag/inheritance requirement | W1 |
| W3 — Reference storage pilot | Existing AST owner accessors and managed reference adapters | One node family with direct/column access and a sparse hash-backed attribute; exact result and lifetime parity | W2 |
| W4 — Collection policy adapter | AdaptiveMap/Set and semantic CollectionPlan | Current linear/chained-hash/AVL choices use the same resolved policy and explain rejections | W1; W2 for managed attributes |
| W5 — Observation extension | Planned trace facade, existing capture and `.sprof` owners | Versioned field/collection/node records, admission, loss accounting and bounded aggregation | W0; XRay stage-1 prerequisites |
| W6 — Three-family integration slice | Compiler driver, node pilot, collection adapter and profiler | One workload captures all three families into one correlated profile and consumes a validated plan | W3–W5 |
| W7 — Native layout/PGO expansion | Storage producer/projection, backend and LLVM/provider adapter | Qualified source bindings, reads/writes, field widths and backend combinations; next-build comparison | W2, W5; W6 reference result |
| W8 — BuildRunner/cache adoption | Existing task owner, contexts, artifacts and cache contracts | Region/object mapping, frozen plans, receipts, semantic/physical invalidation and worker parity | W3–W6; existing cache/resource gates |
| W9 — General live migration | Storage/container owner and reclamation layer | Transactional migration, budget/failure handling and lease tests; no callback migration | W6–W8 and admitted progress protocol |
| W10 — Provider expansion and rollout | Staged XRay provider owners and platform CI | Linux Simple-owned, then Windows Simple-owned qualification under the same public contract | Established Linux LLVM contract; platform-specific evidence |

W1/W4 and the provider work can proceed in parallel after contract ownership is agreed. W9 is not a prerequisite for useful offline PGO; do not hold basic source/config/accessor support hostage to universal live migration. Adding sorted-array or a new hash algorithm is a separate measured extension after W4, not a rewrite of the whole system.

### 14.2 Proposed new artifacts and existing integration points

Use a small shared schema/policy module in the existing compiler/common or structural-data ownership layer; choose exact new paths during W0. New filenames below are **suggestions**, not files claimed to exist:

- `data_schema_contracts.spl`: logical schemas/attributes, construction facts and qualified identities.
- `resolved_data_policy.spl`: references existing layout/collection plans and retains provenance.
- `data_observation_contracts.spl`: versioned metrics/capability descriptors, without file I/O.
- `data_policy_explain.spl`: cold diagnostics/decision receipts at the app/driver boundary.

Keep storage implementation in the existing structural/collection/node owners, profile I/O under the current app/profile boundary, and instrumentation in the existing AOP/backend/provider layers. Do not create a parallel compiler under a new feature directory. Reuse existing task and resource contracts for orchestration.

### 14.3 Minimum useful vertical slice

The first end-to-end deliverable should include:

1. One logical record/node schema declared in SPL and in an equivalent SDN configuration, with identical canonical type results.
2. An existing AST pool exposed through generated `source_span`/child/scalar accessors and whole-node construction, plus one sparse hash-backed analysis attribute. Prove direct/column/hash storage parity where each is semantically admitted; distinguish a missing physical entry from an explicitly stored optional `None` according to the declared schema.
3. One symbol set/map exercising real linear, hash and admitted ordered representations.
4. An AoS/SoA reference comparison and, separately, a qualified native layout pilot.
5. One shared capture manifest/profile containing field, collection and traversal observations with explicit provider/coverage status.
6. A report-only recommendation followed by next-instance or next-build application, exact result comparison and cost report.
7. A BuildRunner task context carrying the frozen plan and qualified region/object identity without bypassing result validation.

Require a real combined native layout/XRay test before marking item 4 plus item 5 as native integration. If the first slice only combines reference layout with an admitted provider, label that limitation rather than silently borrowing evidence from unrelated tests.

### 14.4 Decision output

For every proposed change, the developer-facing explanation should show: site/schema, current representation, eligible and rejected candidates, semantic/progress gates, profile identity and coverage, estimated/measured cost, peak-memory requirement, selected application boundary, and effective source/config provenance.

The same explanation must be available to compiler diagnostics, an app/CLI view and LSP without each re-running a different heuristic. Exact command spelling is left to the existing CLI owner; this report does not advertise unimplemented commands as usable today.

## 15. Acceptance, performance, and formal verification

### 15.1 Required behavioral and failure tests

Test identifiers below define a proposed acceptance inventory. They are **not passing test results**. Implement them in the repository's existing SSpec/unit/integration/native harnesses and retain source-matched execution receipts.

| IDs | Required cases and expected result |
|---|---|
| ATTR-01–03 | Same name/same canonical type merges; different type/qualifier fails with both provenances; distinct nominal IDs do not unify |
| ATTR-04–06 | SPL-only and SDN-only schemas yield equivalent surface; conflicting source/config pins fail; unauthorized external schema injection fails |
| ATTR-07–09 | Required fields missing at finish fail soundly; ordinary unresolved drop is diagnosed; explicit discard and cancellation clean up exactly once |
| ATTR-10–12 | Optional `None` is a valid value; repeated initialization is rejected; defaults do not overwrite explicit initialization |
| ATTR-13–15 | Computed/forwarded properties need no dummy assignment bits; getter-only properties reject writes; ordinary non-opted-in value types keep their semantics |
| ATTR-16–18 | Receiver/RHS/index evaluated exactly once; nested/indexed places and move-only fields behave correctly; cross-engine evaluation order agrees |
| ATTR-19–21 | Region expiry, node reuse and wrong-store handles fail; generation exhaustion never revives stale handles; no mandatory public tag field |
| ATTR-22–24 | Tree cycle/parent/order rules enforced; group graph finalization cannot leak pending dereferences; later analysis results do not corrupt core readiness |
| ATTR-25–27 | Direct/column/hash-backed logical property results agree; sparse absence does not flatten an explicitly present optional value; failed/retried default evaluation does not double-initialize |
| AOP-01–03 | `get`/`set` match canonical symbols across source/config; whitespace/Boolean selector variants agree; accepted but unsupported forms fail explicitly |
| AOP-04–06 | One logical event per successful operation; no helper/backing-map double advice; init/failed writes/migration are not ordinary successful setters |
| AOP-07–09 | Static safety identical with observers off/on; callback recursion/failure/loss bounded; private mutation authority cannot be bypassed by advice |
| LAY-01–03 | AoS↔SoA round trips preserve values/IDs; empty/singleton/boundary sizes and mixed widths/alignment checked; AoSoA tails/block widths qualified separately |
| LAY-04–06 | Address-observed/FFI/volatile/pinned inputs reject conversion; no invented alias facts; unsupported producer/backend combination rejected |
| LAY-07–09 | Reads, writes and compound updates agree across reference/native lanes; loop/control-flow/alias cases tested; code/map survives admitted optimization/LTO |
| COL-01–03 | Every directed transition among linear/hash/ordered preserves exact keys/values; set uniqueness retained; present optional value differs from absent key |
| COL-04–06 | Observable iteration/update order retained; adversarial hash/comparator cases handled; current aggregate-key restrictions enforced |
| COL-07–09 | Explicit unsupported algorithm errors; `auto` retains safe original when evidence is missing; no mutation/migration hidden in shared frozen lookup |
| XR-01–03 | Absent instrumentation, wrong map/build or unsupported ABI fails closed; source/schema/profile versions match; static-off artifacts lack unexpected dependencies |
| XR-04–06 | Raw activation gaps and dropped events marked; paired mode rejected without capability; invalid/missing counters never interpreted as zero |
| XR-07–09 | Record overflow and budget exhaustion are bounded; simultaneous sessions obey Busy/isolation contract; stop/drain/release cannot use expired buffers/maps |
| XR-10–12 | Interpreter/native domains kept distinct; inlining/vector batches report honest coverage; capture cannot expose raw values/pointers by default |
| MIG-01–03 | OOM/cancel/validation failure before publish leaves old root authoritative; all columns/indexes publish consistently; retirement waits for admitted readers |
| MIG-04–06 | Move/drop ownership preserved; incompatible leases block migration; stale proposals and blind post-publication rollback rejected |
| MIG-07–09 | Failure injection around owned-element transfer is safe or the recipe is rejected; non-cancellable commit obeys its contract; old-root readers satisfy the promised snapshot/current-state consistency |
| RUN-01–03 | Cross-run/profile context cannot leak; stale attempt/region results rejected; success requires validated outputs and result receipts |
| RUN-04–06 | Task DAG semantics preserved; owner-only state transitions enforced; 3,000-key and simultaneous-request stress respects the admitted resource/progress policy |
| CACHE-01–03 | Semantic changes invalidate dependents; representation-only changes rebuild physical artifacts correctly; instrumented/uninstrumented keys cannot collide |
| CACHE-04–06 | Incomplete `.rr` rebuilds/fails closed; schema/intro manifests affect the right surface; codec/version/bounds/corruption checks reject unsafe artifacts |
| CACHE-07–09 | Loading one artifact twice rebinds fresh ownership; wrong-snapshot references fail; replayed runtime generations/tokens cannot revive old handles |

Test both positive behavior and refusal paths. A parser-only test cannot establish native lowering, and a grep/structural assertion cannot substitute for running the relevant path. Existing authored specs or tracked implementation files remain distinct from executed evidence.

### 15.2 Performance experiment design

Measure before selecting defaults. Suggested cardinalities are 0, 1, 4, 8, 16, 64, 256, 3,000 and larger memory-bounded cases; these are test points, not automatic algorithm thresholds. Include tiny high-frequency maps, large scan-heavy tables, sparse attributes, high-degree nodes and high-churn regions.

| Dimension | Required comparison |
|---|---|
| Data form | AoS/SoA and admitted AoSoA; linear/chained hash/AVL; dense/sparse node attributes |
| Operation mix | Whole-row vs field scan; hit/miss; insert/remove; ordered traversal; repeated passes |
| Workload stage | Cold/warm cache, construction/steady state, parse/resolve/lower/build orchestration |
| Observation mode | Static off, prepared-disabled, active selected events; record size/loss/coverage |
| Application mode | No switch, next instance/build, exclusive conversion, separately admitted shared migration |
| Resource result | Wall/CPU time, throughput, p50/p95/p99 where meaningful, allocations, peak RSS, bytes copied, retained old epochs |
| Build result | Cold and incremental compile time, cache hits, object size, generated code/map size and reproducibility |

Repeat runs with stated warmup, target/OS/compiler/flags, workload identity and uncertainty. Compare with the existing representation as well as candidates; include the cost of retained boundaries, profiling, profile decoding and migration. Report stalled-reader memory separately from steady-state storage size.

Publish measured rollout budgets during W6/W7 rather than inventing speedup claims now. A candidate is promoted only after a reproducible improvement under agreed latency/memory/instrumentation budgets and semantic tests. No benchmark or speedup was produced for this report.

### 15.3 Formal/refinement obligations

Use small models tied to concrete implementation invariants, plus executable cross-backend tests:

- **Schema preservation:** every admitted access has the declared type/applicability; physical choice cannot change it.
- **Initialization:** no ordinary ready-node access can read an uninitialized required stored field; finish/discard discharges construction exactly once.
- **Projection:** checked logical IDs resolve within the correct live region/store and admitted layout bounds; address calculations cannot overflow.
- **Lookup equivalence:** each representation has the same abstract key/value relation, optional presence and observable ordering.
- **Migration:** every visible root describes one complete logical state; no lost/duplicated keys or mixed column epochs; failures preserve the old state before publication.
- **Lifetime:** node/region reuse cannot make a stale qualified reference valid; reclamation follows all admitted readers.
- **Policy monotonicity:** performance selection cannot weaken hard ownership, ABI, memory or progress constraints.
- **Observation noninterference:** disabling optional observation does not remove semantic checks or change logical results; partial evidence cannot masquerade as exact.

Model proof does not automatically prove emitted machine code. Tie each claim to the actual SPL/runtime/backend implementation and independently qualify ABI preservation and patching. Keep mandatory release safety unless a valid static proof removes a specific check; a debug-only generation guard is not sufficient.

### 15.4 Completion gates

Basic integration is complete only when W1–W6 have source-matched executed evidence and one common profile/config decision can be traced through all three families. Native optimization requires its combined backend/provider evidence; BuildRunner deployment requires W8 receipts and failure tests; shared live migration requires W9. Windows fixture success alone satisfies none of those application integration gates.

The current adopted tracing policy keeps code/providers/maps resident. Do not add hot-unload testing as a prerequisite for that resident design; reopening unload support requires a separate lifecycle contract. Session admission, generation, drain and buffer reclamation remain mandatory now.

## 16. Sources and completion boundary

### 16.1 Evidence scope

Repository links below are pinned to the inspected revision, rather than floating branch URLs. Targeted compiler/layout and collection/runner files were rechecked against the earlier audit; the inspected capability limits remained. The material XRay update is the merged experimental Windows verification work, with qualifications stated in section 10.

This is a read-only source-and-plan audit with a proposed integration design. No compiler binary was built, no repository test suite or benchmark was run, and no production XRay session or data migration was executed for this report. Previously published native CI evidence is identified separately. A requirements/specification file describes intent or test inventory unless accompanied by a matching execution receipt.

### 16.2 Pinned repository sources

- **R01 — Language: no implementation inheritance.** [Syntax quick reference](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/07_guide/quick_reference/syntax_quick_reference.md); [No-inheritance ergonomics](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/01_research/language/traits/no_inheritance_ergonomics_2026-02-16.md).

- **R02 — Existing AST pools and owner accessors.** [Expression nodes](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/_AstExpr/nodes.spl); [Statement nodes](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/ast_stmt.spl); [Declaration nodes](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/_Ast/decl_nodes.spl).

- **R03 — Pointer-free cached AST contract.** [FileAstV1](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/00.common/cache_contract/file_ast_v1.spl); [Frontend projection builder](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/cache_artifact/file_ast_builder.spl).

- **R04 — Interpreter access paths.** [Rust field/property resolution](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler_rust/compiler/src/interpreter/expr/calls.rs); [Pure-Simple access evaluation](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/interpreter/eval_access.spl); [Exported access/assignment helper](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl).

- **R05 — HIR fields and source layout attributes.** [HIR definitions](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/20.hir/hir_definitions.spl); [Class declaration lowering](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/20.hir/hir_lowering/_Items/class_declaration_lowering.spl); [Current layout attributes](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/00.common/_Attributes/layout_attrs.spl).

- **R06 — Canonical layout vocabulary.** [Storage layout contracts](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/storage_layout_contracts.spl).

- **R07 — Layout planning, mapping and safety policy.** [Static planner](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/planner.spl); [Checked mapping](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/mapping.spl); [Reference conversion oracle](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/reference_conversion.spl); [Memory-policy schema](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/00.common/parallel_policy/policy_schema.spl).

- **R08 — Narrow native layout pipeline and capability guards.** [Storage access facts](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/storage_access_analysis.spl); [Layout advisory](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/storage_layout_access_advisory.spl); [Typed view declaration](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/typed_storage_view_declaration.spl); [Typed view producer](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl); [Projection lowering](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl); [Backend helper guards](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/70.backend/backend/backend_helpers.spl); [Native x86-64 emission](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/70.backend/backend/native/isel_x86_64.spl); [Compiler-private pilot](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/80.driver/driver_typed_storage_pilot.spl); [Paired-native/LLVM guard](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/80.driver/driver_build/group_native_compile_pairs.spl).

- **R09 — Adaptive container source implementations.** [AdaptiveMap](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/collections/adaptive_map.spl); [AdaptiveSet](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/collections/adaptive_set.spl); [AdaptiveTextSet](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/collections/adaptive_text_set.spl).

- **R10 — Current concrete map algorithms.** [Chained Map](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/map.spl); [Array-backed AVL OrderedMap](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/collections/ordered_map.spl).

- **R11 — Source annotations and existing feedback identity.** [Collection feedback resolver](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/collection_feedback.spl); [Feedback guide](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/07_guide/language/profile_switchable_container_feedback.md); [Requirements and qualification limits](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/02_requirements/feature/profile_switchable_container_algorithms.md).

- **R12 — Typed selection and narrow executable consumer.** [Semantic CollectionPlan selection](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/35.semantics/perf/collection_plan_selection.spl); [Literal membership MIR consumer](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/50.mir/_MirLoweringExpr/collection_literal_membership.spl); [General integration gap tracker](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/08_tracking/bug/profile_switchable_typed_plan_unwired_2026-10-01.md).

- **R13 — Capture ABI, current recorder and profile ownership.** [Collection capture facade](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/sffi/collection_capture.spl); [Runtime capture implementation](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/runtime/runtime_collection_capture_impl.h); [Collection .sprof ingestion](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/app/optimize/sprof_collection_profile.spl); [Run boundary](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/app/io/collection_profile_run.spl); [Architecture and remaining coverage](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/04_architecture/compiler/profile_switchable_container_algorithms.md).

- **R14 — AOP selectors, matching and execution.** [Selector validator](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/aop_predicate_parser.spl); [Compiler matcher](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/aop.spl); [MIR advice insertion](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/50.mir/mir_aop_injection.spl); [Interpreter matcher/advice](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/70.backend/backend/interpreter_aop_weave.spl); [Semantic join-point model](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/35.semantics/join_point_model.spl).

- **R15 — Task owner and BuildRunner receipts.** [Parent scheduler](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/task_runner/scheduler.spl); [Task contracts](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/task_runner/contracts.spl); [Build task context](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/app/buildrunner/task_context.spl); [Task database/result admission](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/app/buildrunner/task_database.spl); [Runner architecture](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/04_architecture/task_runner_buildrunner.md).

- **R16 — Region transfer versus existing ID carriers.** [TransferEnvelope contracts](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/transfer/transfer_contracts.spl); [Engine local generational NodeId](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/engine/ids.spl); [Formal-model ObjId carrier](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler_rust/lib/std/src/verification/models/gc_manual_borrow.spl).

- **R17 — Accessor cleanup tooling.** [Accessor easy-fix implementation](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/tooling/easy_fix/accessor_core.spl).

- **R18 — Merged experimental Windows XRay evidence.** [Experimental workflow](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/.github/workflows/xray-windows-native-verification.yml); [Native scalar harness](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/test/integration/xray/windows_native_integration.cpp); [Bounded x64 trampoline](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/test/integration/xray/trampoline_x64_bounded.S); [Separate ABI regression](https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/test/integration/xray/abi_state_regression.cpp).

For R18, also see the [merged PR #5962](https://github.com/ormastes/simple/pull/5962), [expanded verification run](https://github.com/ormastes/simple/actions/runs/41554579305), [native x64 job](https://github.com/ormastes/simple/actions/runs/41554579305/job/125650220036), and [native ARM64 job](https://github.com/ormastes/simple/actions/runs/41554579305/job/125650219654). That run tested `4d36e39f08a49a23642766f09bcc692c44dde242`; its fixture changes are included in the inspected merge. It is not a fresh execution of the merge commit performed for this report.

### 16.3 Prior project plans reconciled

- **D01 — [Adaptive collections design plan (2026-09-16)](https://chatgpt.com/library?file_id=libfile_5b7f757c91a8819188feab57dddc8e87&account_id=personal).**

- **D02 — [Typed dataframe, collections and query optimizer design (2026-09-16)](https://chatgpt.com/library?file_id=libfile_fd90ee32b1ec8191b31d5fee9e1f8c2b&account_id=personal).**

- **D03 — [Cache with SCV implementation plan, revisions including reverse-reference rules (2026-10-27)](https://chatgpt.com/library?file_id=libfile_a25b812bd9608191bd5cf0abecacd317&account_id=personal).**

- **D04 — [Concurrent resources and runner plan (2026-10-27)](https://chatgpt.com/library?file_id=libfile_c92389142d90819183b450f05db04b21&account_id=personal).**

- **D05 — [Staged XRay design (2026-11-03)](https://chatgpt.com/library?file_id=libfile_99e7b3800b0881918c682b6f3a9c19a1&account_id=personal).**

- **D06 — [Aspect and visibility improvement plan](https://chatgpt.com/library?file_id=libfile_e766d02fd61c8191bb792827af412970&account_id=personal).**

These plans supply project constraints and intended architecture, not proof that each proposed feature is implemented. This report supersedes conflicting examples only for the requested data/attribute/XRay integration: no implementation inheritance, no mandatory public node tag, whole-node initialization, common source/config resolution, and resident staged tracing.

### 16.4 External primary references

- **E01 — [LLVM XRay documentation](https://llvm.org/docs/XRay.html).** Function instrumentation, activation and custom/typed event facilities; upstream capabilities are not evidence of Simple integration.

- **E02 — [LLVM XRay FDR format](https://llvm.org/docs/XRayFDRFormat.html).** Event/record interpretation and recording constraints; profile completeness must be explicit.

- **E03 — [Abseil container guide](https://abseil.io/docs/cpp/guides/container).** Concrete container invalidation/stability trade-offs; illustrative precedent, not a dependency requirement.

- **E04 — [AspectJ join-point semantics](https://eclipse.dev/aspectj/doc/released/progguide/semantics-joinPoints.html).** Field get/set as logical join-point precedent; not Simple syntax support.

- **E05 — [MLIR operation definition specification](https://mlir.llvm.org/docs/DefiningDialects/Operations/).** Generated typed accessors/builders/verifiers as a design precedent; not a proposal to replace Simple with MLIR.

Additional algorithm background: [Abseil B-tree design](https://abseil.io/about/design/btree). Alternative algorithms in section 7 remain candidates until implemented and qualified in Simple.

### 16.5 Final recommendation

Implement **one typed logical attribute surface, one composed data-policy resolver and one versioned observation/profile path**. Reuse existing AoS/SoA contracts, adaptive collection implementations and node pools. First ship the three-family reference/next-build slice; expand native backend coverage and live migration only through explicit capability and correctness gates.

The deliverable of this task is this consolidated Markdown plan. Repository implementation and original plan files were not modified. The next authorized implementation task should start with W0/W1 plus the small W3/W4 pilot, not an all-at-once container/runtime rewrite.

[R01]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/doc/07_guide/quick_reference/syntax_quick_reference.md
[R02]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/_AstExpr/nodes.spl
[R03]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/00.common/cache_contract/file_ast_v1.spl
[R04]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler_rust/compiler/src/interpreter/expr/calls.rs
[R05]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/20.hir/hir_definitions.spl
[R06]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/storage_layout_contracts.spl
[R07]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/storage_layout/planner.spl
[R08]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/60.mir_opt/mir_opt/storage_access_analysis.spl
[R09]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/collections/adaptive_map.spl
[R10]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/src/map.spl
[R11]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/collection_feedback.spl
[R12]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/35.semantics/perf/collection_plan_selection.spl
[R13]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/sffi/collection_capture.spl
[R14]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/compiler/10.frontend/core/aop_predicate_parser.spl
[R15]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/task_runner/scheduler.spl
[R16]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/common/structural/transfer/transfer_contracts.spl
[R17]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/src/lib/nogc_sync_mut/tooling/easy_fix/accessor_core.spl
[R18]: https://github.com/ormastes/simple/blob/0e4d613ab46a3af12e2111c480b1c1db9f6dc513/.github/workflows/xray-windows-native-verification.yml
[D01]: https://chatgpt.com/library?file_id=libfile_5b7f757c91a8819188feab57dddc8e87&account_id=personal
[D02]: https://chatgpt.com/library?file_id=libfile_fd90ee32b1ec8191b31d5fee9e1f8c2b&account_id=personal
[D03]: https://chatgpt.com/library?file_id=libfile_a25b812bd9608191bd5cf0abecacd317&account_id=personal
[D04]: https://chatgpt.com/library?file_id=libfile_c92389142d90819183b450f05db04b21&account_id=personal
[D05]: https://chatgpt.com/library?file_id=libfile_99e7b3800b0881918c682b6f3a9c19a1&account_id=personal
[D06]: https://chatgpt.com/library?file_id=libfile_e766d02fd61c8191bb792827af412970&account_id=personal
[E01]: https://llvm.org/docs/XRay.html
[E02]: https://llvm.org/docs/XRayFDRFormat.html
[E03]: https://abseil.io/docs/cpp/guides/container
[E04]: https://eclipse.dev/aspectj/doc/released/progguide/semantics-joinPoints.html
[E05]: https://mlir.llvm.org/docs/DefiningDialects/Operations/