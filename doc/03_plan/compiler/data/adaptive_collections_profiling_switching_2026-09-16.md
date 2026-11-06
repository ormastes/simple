# Simple Adaptive Collections
## Unified profiling, in-place attributes, and safe physical-plan switching

**Design and implementation-plan report — 16 September 2026**  
**Repository audited:** `ormastes/simple`  
**Pinned source revision:** `6a133cf2bd2589a6a62f6c83ec7f10f932084e64`  
**Status:** proposed design grounded in a static source audit and primary-source research. No Simple build, test, benchmark, or device run was executed for this report. Existing implementation, existing plans, and new proposals are distinguished below. All new attribute names, configuration schemas, IR records, and command-line examples are proposals, not claims of currently supported interfaces.

### Review notes (reviewed 2026-11-06 against `origin/release/1.0.0` @ `8991bc5067d`)

This plan is older than its sibling [`data_attributes_layout_containers_xray_2026-11-06.md`](data_attributes_layout_containers_xray_2026-11-06.md) ("the data plan"); where the two overlap, the data plan is the owner. What changed in place:

- **Stale since the pin:** `.sprof` already has a `sprof-v2` collection-workload envelope (`src/app/optimize/sprof_collection_profile.spl`; `sprof_loader.spl:190`), so "new collection records are not already accepted" is no longer true (§1, §11.1); the live CollectionPlan owners are `src/compiler/35.semantics/perf/collection_plan*.spl` and `src/compiler/60.mir_opt/mir_opt/{collection_plan_selection,collection_plan_explain,perf_facts}.spl` — there is no `20.hir/perf` and no `60.mir_opt/collection_plan/` (§1, §6.1, §17); `config/compiler/collection_operations.sdn` exists but is an empty `pending-admission-v1` snapshot; `AdaptiveMap` lookups still promote in place (`promote_if_useful`) with no lock.
- **Owner decisions bound in:** generics are erased and Mono is deleted — the "monomorphize when known" sentence in §3.2 is removed; trace code is resident until process exit — §6.3's "provider unloading" is removed; collection telemetry modes (§10.1) are selected through aspect params, the runtime switch, never through a new SDN mode key (`--xray`/`trace.instrumentation` is the only static switch); lockless by default — §14.1's exclusive-owner transition is unique ownership, not a mutex.
- **Unified with the data plan:** one resolver (`ResolvedCollectionPolicyV1` is the collection row of the data plan's W1 envelope, §5.2); the `@col`/`@col_site`/`@col_policy`/`@col_impl` quartet collapses onto the existing `@collection_algorithm` plus at most one site label (§4.1); one switching-mode table (data plan §11.1, referenced from §13); one session identity (`observer_session_v1.spl` + loader `run_id`/`workload_id`, §8.1/§11.1); `ProfileSessionV2` is withdrawn (name collides with the shipped `sprof-v2`).
- **Out of scope / cuts:** §3.1 set literals and the §3.2 `col<T>` hierarchy are separate language proposals, not packages of this plan; §12.1 candidates beyond linear / chained hash / AVL / sorted flat are inventory; C9 (SIMD/GPU execution) is blocked and not part of this program; C10 is deferred behind C7.
- **TDD/SSpec plan added (§21):** first failing spec per package C0–C10, mapped onto the §18.1 correctness matrix; unified order with W0–W10 lives in the data plan §17.4.

## Contents

- [1. What the repository actually contains](#1-what-the-repository-actually-contains)
- [2. Research findings and what to adopt](#2-research-findings-and-what-to-adopt)
- [3. Language surface: retain meaning, reduce spelling](#3-language-surface-retain-meaning-reduce-spelling)
- [4. In-place source attributes: a V1 requirement](#4-in-place-source-attributes-a-v1-requirement)
- [5. One source-and-SDN policy model](#5-one-source-and-sdn-policy-model)
- [6. Improved architecture and ownership](#6-improved-architecture-and-ownership)
- [7. How perf profiling and collection profiling cooperate](#7-how-perf-profiling-and-collection-profiling-cooperate)
- [8. Identity, attribution, and profile stability](#8-identity-attribution-and-profile-stability)
- [9. Collection measurements: enough information to plan correctly](#9-collection-measurements-enough-information-to-plan-correctly)
- [10. Low-overhead collection instrumentation](#10-low-overhead-collection-instrumentation)
- [11. `.sprof` evolution and data integrity](#11-sprof-evolution-and-data-integrity)
- [12. Physical candidates and cost model](#12-physical-candidates-and-cost-model)
- [13. Switching modes: separate them explicitly](#13-switching-modes-separate-them-explicitly)
- [14. Migration protocol and semantic safety](#14-migration-protocol-and-semantic-safety)
- [15. SIMD, GPU, and existing layout integration](#15-simd-gpu-and-existing-layout-integration)
- [16. Examples of end-to-end decisions](#16-examples-of-end-to-end-decisions)
- [17. Implementation plan and parallel work packages](#17-implementation-plan-and-parallel-work-packages)
- [18. Verification and benchmark plan](#18-verification-and-benchmark-plan)
- [19. Developer workflow and inspectability](#19-developer-workflow-and-inspectability)
- [20. Decisions, risks, and completion criteria](#20-decisions-risks-and-completion-criteria)
- [21. TDD and SSpec plan (reviewed 2026-11-06)](#21-tdd-and-sspec-plan-reviewed-2026-11-06)

## Executive decision

**Use one profiling architecture with several independently selectable collectors, not one universal hot-path recorder and not a second collection profiler.** Collection operation counts, allocation/copy data, field-access summaries, timing regions, and CPU/GPU samples should share session and identity metadata. They must retain their different meanings: a CPU sample is not a lookup count, an inclusive region time is not exclusive container time, and a profile is never a correctness proof.

Make `col<T>` a short collection capability/alias, not a new reserved keyword or a universal dynamically dispatched object. Keep ordinary collection syntax and semantic families. Add representation freedom only where existing semantics, ownership, ABI, and backend support allow it. A sequence remains a sequence even when it acquires a hash index; a set remains exact even when its representation changes.

Support **local, in-place source attributes in the first functional release**, alongside SDN rules targeting creation sites. Both lower to one immutable `ResolvedCollectionPolicyV1`. Source hints, project policy, and profiler-generated advice must not become three unrelated configuration systems. Continue using the existing `@layout(...)` family and compose the existing frozen `StorageLayoutPlanV1`; do not replace or silently extend that contract.

Recommended implementation order:

1. Establish semantic contracts, stable origin IDs, local-attribute binding, SDN composition, and versioned profile records.
2. Ship correlated reports and offline recommendations before enabling transformations.
3. Enable verified AOT/creation-time specialization, then bounded runtime representation transitions.
4. Integrate admitted typed-storage layouts and SIMD; admit GPU layouts and execution only with real backend, transfer, and synchronization evidence.

This is an extension of the repository's existing CollectionPlan/performance program, not a replacement architecture. [R1], [R7], [R8], [R10]

---

## 1. What the repository actually contains

The audit read selected source files at the pinned revision. It did not infer implementation from feature names alone or treat design documents as executable evidence.

| Area | Observed source or documented status | Consequence for this work |
|---|---|---|
| `.sprof` loading | `sprof_loader.spl` implements `sprof-v1` (module/workload identification, bounded diagnostics, saturating merge, function/block/edge records) and, since the pin, accepts the `sprof-v2` version string (`:190`); the collection-workload records are decoded by the sibling `sprof_collection_profile.spl`, while the loader's own record validator still admits only function/block/edge (`collection_size`, `lookup_count`, `distinct_key_count`, `loop_trip_count`, `collection_sample_limit`). | *Review 2026-11-06:* collection records **are** accepted now. Field/node observation records are not; they are the data plan's W5 extension of this envelope. [R1] |
| Native profile transport | `native_profile_counter_runtime.spl` maps counter slots and metadata to the same limited record families. | Extend the counter/metadata path and consolidate codecs; do not add another independent exporter. [R2] |
| Region timing profiler | `90.tools/perf/profiler.spl` reads a monotonic clock and updates a text-keyed dictionary of counters; it exports JSON. | Preserve the API and add a shared-session adapter. This is too much work to perform around every collection lookup. [R3] |
| Compiler-stage adapter | `85.mdsoc/.../profiler_adapter.spl` currently records completed-stage count and last stage. Its inspected implementation does not measure durations. | Keep compiler-stage events distinct from actual timing and from profiling the generated program. [R4] |
| JIT profile consumer | `sprof_hotspot_bridge.spl` already reuses function counts for hotspot decisions and deliberately avoids a compiler-to-app import. | Preserve that dependency direction. Add typed collection-profile queries rather than importing the app loader into the optimizer. [R5] |
| Optimizer integration | `optimizer_plugin.spl` has real descriptors for source/MIR scope, static/dynamic application, and cost classes. | Use its registry and activation discipline; a registered descriptor alone does not establish an active transform. [R6] |
| Collection/performance program | The detailed design already proposes one typed-HIR collector, shared `PerfFacts`, logical/physical CollectionPlan, `.sperf`, optional `.sprof-v2`, and an operation registry. | *Review 2026-11-06:* the landed owners are `src/compiler/35.semantics/perf/` (`collection_plan_selection.spl` with `CollectionPlanAlgorithm {Original, Linear, Hash, Ordered}`, `collection_plan_{analysis,explain,extractor,loop}.spl`) and `src/compiler/60.mir_opt/mir_opt/{collection_plan_selection,collection_plan_explain,perf_facts}.spl`; the only executable MIR consumer is `50.mir/_MirLoweringExpr/collection_literal_membership.spl`. Extend these; `20.hir/perf` and `60.mir_opt/collection_plan/` do not exist and are not to be created. [R7] |
| Layout contract | `StorageLayoutPlanV1` and `StorageLayoutKind` exist, including AoS, SoA, AoSoA, Grouped, Tiled, Packed, FactoredIndex, and ExternalFixed. | Compose the frozen contract from the collection physical plan. [R8] |
| Automatic layout heuristic | `storage_layout_plan_auto` already selects layouts using ABI pinning, field independence, SIMD width, and count. | Add calibrated profile/cost inputs through a versioned adapter; distinguish a selected enum from available lowering. [R9] |
| Layout reachability | The storage-layout owner documents guarded typed-view/projection work and custom x86 native lowering, but public typed `T[]` binding, complete field rewriting, other backends, and PGO/view-cache integration remain incomplete. | No blanket claim that ordinary arrays can already switch layout. Start only with admitted typed storage and explicit backend capabilities. [R10] |
| Generic map | `src/lib/nogc_sync_mut/src/map.spl` defines `Map<K,V> where K: Hash + Eq`, using bucket lists and cached hashes. | Generic map code exists. Audit and reuse it rather than assuming only the text-only HashMap exists. [R11] |
| Literal parser | The inspected seed parser routes `{...}` to dictionary parsing and returns an empty Dict for `{}`. Nonempty entries expect a colon. | Set literals require an additive parser change. Reinterpreting existing empty braces would break compatibility. [R12] |
| Attributes | The inspected `@name(args)` helper recognizes identifiers and scalar literals; this does not prove all local bindings or named arguments preserve attributes end-to-end. | Reuse punctuation and simple arguments, but explicitly implement and test local binding retention. Reject unsupported collection arguments rather than dropping them. [R13] |
| SDN | A shared SDN parser/schema implementation exists. A general recursive include/override contract was not verified in this audit. | Specify composition at the policy-loader layer. Do not present `include "..."` as established SDN syntax. [R14] |

### Corrections to earlier assumptions

AoS/SoA support is already a foundation, not a new subsystem. Conversely, a layout contract does not establish universal public-array conversion. Generic map source exists, but its presence does not establish backend parity, optimal memory use, or a switchable ABI.

The current JIT bridge uses source availability as a coarse input to `typed_mir`/`safe_deopt` fields. New collection specialization must require actual validated IR and deoptimization/materialization evidence; source text alone is insufficient. This is a requirement for the new transform, not a claim that every existing JIT route is unsafe. [R5]

---

## 2. Research findings and what to adopt

The relevant work spans collection specialization, data-structure synthesis, memory-layout abstraction, and compiler profiling. No single cited system establishes the entire proposed Simple feature.

| Primary source | Established mechanism | Adoption for Simple | Boundary |
|---|---|---|---|
| **Makor et al., 2025 — Automated Profile-Guided Replacement of Data Structures** | Allocation-site-specific profiling drives customized Java data-structure allocations in GraalVM Native Image. | Profile by creation origin; specialize allocations offline first. | Memory results are workload-specific; not evidence for arbitrary live layout migration. [P1] |
| **Loncaric, Ernst, Torlak, ICSE 2018 — Generalized Data Structure Synthesis / Cozy** | Query synthesis and incrementalization account for both queries and state updates across related collections. | Cost index maintenance as well as lookups; allow packed primary storage plus secondary indexes. | Full synthesis is optional future work, not a prerequisite for a bounded candidate planner. [P2] |
| **LLAMA, 2022** | Separates logical record access from physical mappings and supplies layout-aware copying. | Reuse logical projections; specialize accessors rather than materializing record objects for every field access. | Compile-time mapping abstraction is not automatically a runtime migration controller. [P3] |
| **LLAMA/AdePT, 2023** | Field read/write instrumentation and heatmaps complement traditional GPU profiles. | Join collection/field profiles with general performance evidence. | Fine-grained traces can be expensive; use bounded, selective collection. [P4] |
| **Radtke and Weinzierl, 2025 extended paper** | Local annotations guide temporary AoS/SoA views and GPU offload; the compiler handles selected-field conversion. | Support in-place attributes and phase-local views, not only whole-object replacement. | The paper leaves the heuristic decision of when to convert to the developer. Simple's automatic profitability model is additional work. [P5] |
| **PyPy storage strategies** | Specialized collection representations can fall back to general ones without changing application semantics. | Every specialization needs a defined valid-operation fallback. | Type-driven strategy changes are narrower than arbitrary workload-driven switching. [P6] |
| **Roaring compressed bitmap research, 2016** | Hybrid packed arrays, bitmaps, and run-length segments adapt at a subcontainer granularity. | Consider chunk-local adaptation for integer sets; avoid converting an entire large collection unnecessarily. | A specialized integer-set technique, not a general map layout. [P7] |
| **Swift collection protocols** | Capabilities separate traversal, multipass access, and stronger random-access guarantees. | `col` as a capability, semantic families distinct from representations. | Protocol conformance does not itself select a hash table or GPU backend. [P8] |
| **Clang PGO documentation** | Sampling and instrumentation have different data and uses; representative workloads matter. | Share correlation metadata without conflating samples, counts, and coverage. | A sampled absence is not proof that a path or mutation is impossible. [P9] |
| **Futhark memory optimization work** | Explicit memory information and dependence reasoning allow elimination of some temporary arrays/copies. | Keep memory/view facts in IR; prove safe direct construction rather than assuming in-place execution is legal. | High-level elementwise syntax alone does not prove lack of cross-element dependencies. [P10] |
| **SoCal / Colobus, May 2026 preprint** | Factored multi-buffer layouts extend SoA-like ideas to serialized recursive ADTs. | Later research lane for compiler ASTs and browser trees. | Not a V1 dependency or a proof of safe arbitrary mutable graph conversion. [P11] |

**Synthesis:** share one logical operation model and one evidence system, but separate four physical decisions: primary representation, indexes, record layout, and execution/residency. Couple their costing; do not couple their semantics.

---

## 3. Language surface: retain meaning, reduce spelling

*Review 2026-11-06:* §3.1 (set literals) and §3.2 (the `col<T>` capability hierarchy) are **not packages of this plan**. Neither exists in the pure-Simple parser or stdlib today, neither is needed to profile or switch existing arrays, dictionaries, `AdaptiveMap`/`AdaptiveSet`, and each is a language-surface proposal that needs its own requirement and parser lane. They are retained as design intent only; no C-package depends on them.

### 3.1 Literal compatibility

| Surface | Intended meaning | Migration rule |
|---|---|---|
| `[a, b, c]` | Ordered sequence, including duplicates | Preserve existing array/sequence behavior and guarantees. |
| `{a, b, c}` | Exact unique collection | Add set parsing and semantic support consistently across parsers/backends. |
| `{k: v, ...}` | Exact keyed collection | Preserve existing dictionary semantics, including observable iteration behavior. |
| `{}` without expected type | Existing empty dictionary | Keep this meaning in the current language mode. |
| `{}` with explicit `Set<T>` expectation | Empty set | Add deliberate contextual typing, or initially require `Set<T>.new()` until parity is complete. |
| `col<T>` | Common collection capability | Ordinary library/trait name, not a reserved token. |

The family notation “`{}` means unique collection” must not silently change old programs. The inspected parser makes the conflict concrete. A later language edition could change defaults with an explicit migration tool, but that is unnecessary for this feature. [R12]

A nonempty brace parser can distinguish a set from a map after the first expression by the presence of a colon. Comprehensions, spread forms, nested braces, multiline expressions, errors, and empty expected-type cases require their own tests. No new lexer token is needed; an additive parser change still is a grammar change.

### 3.2 Capability hierarchy

Use canonical descriptive names in documentation, with `col<T>` as the short alias/capability used by generic APIs. The following is a proposed Simple hierarchy informed by Swift, not a verbatim Swift API:

```text
Iterable<T>                         # may be single-pass
  Collection<T> = col<T>            # multipass collection capabilities
    BidirectionalCollection<T>
      RandomAccessCollection<T>

Orthogonal capabilities:
  MutableElements<T>
  RangeReplaceable<T>
  KeyLookup<K,V>
  UniqueMembership<T>
  ContiguousStorage<T>              # only when actually guaranteed
```

Sequence, Set, and Map are semantic families conforming to appropriate capabilities; a Map's traversed element is an entry/key-value pair. Do not place random access beside bidirectional access as unrelated alternatives. Do not assume every collection has constant-time `count`, integer indexes, mutable elements, or contiguous `T*` storage. [P8], [P8c]

`col<T>` in a generic bound must not be justified by a monomorphization promise: Simple generics are erased and there is no monomorphization pass (Mono is deleted), so a `col<T>` bound costs exactly the ordinary erased dispatch and nothing in this plan may assume otherwise. Avoid making `random`, `con`, or several new abbreviations mandatory; `col` is sufficient for this request. No claim that it is a single token in all LLM tokenizers is needed.

### 3.3 Representation freedom is constrained

A public concrete struct whose `buckets` or byte layout are visible cannot be silently replaced by a different representation. The initial automatic lane should cover compiler-private storage, eligible nonescaping locals, and containers with an admitted opaque-storage contract. Preserve ordinary RuntimeValue arrays until the existing typed-storage integration explicitly admits them. [R10], [R11]

A sequence with frequent membership searches may become “sequence plus index”; it may not become an unordered set and lose duplicates. A collection's semantic type must not change based on a profile or a user's machine. Declared complexity contracts also filter candidates: a generic key-lookup capability may admit sorted lookup, but an interface explicitly promising expected constant-time lookup must not silently lose that promise. The spelling `val` alone must not be used as proof that a collection's key set or reachable values are immutable.

---

## 4. In-place source attributes: a V1 requirement

“In-place attribute” here means an attribute attached at the local creation/binding site. It does **not** promise that changing the memory representation occurs without a temporary allocation.

### 4.1 Proposed local forms

Use the existing `@name(args)` spelling and simple constant arguments. These examples define the proposed interface; end-to-end parser/semantic support is an implementation task.

```simple
@col(auto, lookup_heavy, updates_rare)
@col_site("parser.symbols")
var symbols: {text: Symbol} = {}

@col(auto, scan_heavy, switch_at_boundary)
@layout(soa)
var particles: [Particle] = []

@col_policy("compact_small_set")
var enabled: Set<i64> = Set<i64>.new()

@col_impl(flat_hash)
@col(no_switch)
var fixed_plan: {i64: i64} = {}
```

`@col` holds workload/objective/switch-policy tags. `@col_site` provides an optional stable semantic label. `@col_policy` references a named SDN policy. `@col_impl` is an explicit physical pin. Existing layout attributes keep their own meaning and feed the existing layout resolver.

*Review 2026-11-06 — the quartet above is collapsed; it is four spellings for one resolver input.* The physical pin already exists as `@collection_algorithm("auto"|"linear"|"hash"|"ordered")` (`src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl:1100`) and the creation site already has a stable identity (`ast://{module_key}[/{owner}]/local/{name}#{source_hash}`, `collection_feedback.spl:50-52`). V1 therefore ships: `@collection_algorithm` unchanged as the pin; **at most one** new scalar attribute, `@collection_site("...")`, and only if the owner wants a user-facing label at all (data plan §17.5 Q2); workload hints, objectives and named policies live in SDN rules keyed by site, with no source spelling in V1. `@col`, `@col_policy` and `@col_impl` are withdrawn. The example block above is kept as the pre-review proposal.

Do not rely on unverified `@col(update = rare, ...)` named-argument grammar. A later spelling refinement can be implemented in the general attribute subsystem rather than adding collection-only parsing.

### 4.2 Attribute categories

| Category | Examples | Meaning when the observation or request is wrong |
|---|---|---|
| Workload hint | `lookup_heavy`, `updates_rare`, `scan_heavy`, `build_then_read` | May guide cost; behavior remains correct even if the workload differs. |
| Objective | `compact`, `throughput`, `startup`, `latency` | Selects optimization objective, not a semantic guarantee. |
| Switch permission | `no_switch`, `switch_at_boundary` | Limits when physical changes are allowed. Does not supply alias/safety evidence. |
| Physical pin | `@col_impl(flat_hash)`, explicit fixed layout | Must use an admitted implementation or report an error; never silently ignore a required pin. |
| Semantic/assurance requirement | Existing no-allocation, ownership, ABI, deterministic-order requirements | Must be proved/enforced; cannot be weakened by profile advice. |
| Site identity | `@col_site("parser.symbols")` | Binds policy/profile metadata; duplicate labels in their namespace are diagnostics. |

An `updates_rare` hint is not the same as an enforced immutable-key contract. A mutable map with frozen keys may still replace values without rebuilding an MPHF; inserting a new key requires a separate admitted path.

### 4.3 Local annotations versus true in-place execution

A separate optional `in_place_only` tag can express a real execution constraint without new grammar. It requires a transformation to write its result into an admitted existing destination rather than allocate a replacement payload buffer. Only explicitly budgeted scratch is permitted; a separate no-allocation requirement is stricter and also forbids dynamically allocating that scratch. Payload-buffer reuse does not by itself preserve every field address, so raw-pointer/ABI pins remain stronger constraints.

The compiler must prove overwrite/dependence safety, uniqueness where required, and preservation of logical value semantics. An immutable-looking operation may reuse storage only when the existing ownership/liveness rules permit it. If no legal in-place implementation exists, a required tag produces a diagnostic rather than an allocating fallback. This is distinct from supporting attributes at the creation site, which is mandatory regardless of whether any in-place kernel is admitted.

### 4.4 Attachment and evaluation rules

Attributes on a `val`/`var` describe the logical collection produced by that initializer. They do not apply indefinitely to every future unrelated object assigned to the variable. Field attributes provide a default for collections constructed in that field; factory annotations apply to a declared returned collection origin. Ambiguous multi-result factories require an explicit selector.

Attribute arguments are compile-time data, not runtime decorators. They must not evaluate user callbacks, allocate at lookup sites, or change initializer order. An initializer with multiple hidden collections should require a named result/creation selector instead of spraying the attribute across all allocations.

V1 must support attributes immediately before local declarations, preserve them through AST/HIR/MIR, and display them in IDE diagnostics. Same-line attribute support should follow the general attribute grammar. Arbitrary expression-position attributes are not necessary for V1; ordinary local bindings can name temporary collections without adding a new expression syntax.

Unknown collection tags, invalid values, unsupported attachment positions, or silently lost attributes must be errors. The inspected parser helper's unsupported-argument fallback must not become accepted evidence for a collection policy. [R13]

---

## 5. One source-and-SDN policy model

### 5.1 Normalization

Both inputs produce the same record:

```text
ResolvedCollectionPolicyV1
  semantic_contract_ref
  hard_constraints
  allowed_representations
  workload_hints
  objective_and_resource_budgets
  switch_policy
  layout_policy_ref
  named_policy_dependencies
  per_field_provenance
  canonical_policy_digest
```

A profile produces observations and optional advice, not hard constraints. Source facts such as type, ordering, and proven ownership live outside this policy record and cannot be overridden by configuration.

### 5.2 SDN composition without a new SDN grammar

Use ordinary SDN data fields. The **policy loader**, not the low-level data parser, interprets `includes` and resolves the DAG. The following is a proposed schema:

```sdn
schema: "simple.collection-policy.v1"
includes: ["collections/defaults.sdn", "collections/project.sdn"]
optional_includes: ["collections/generated-advice.sdn"]

collection_policy:
    mode: "advisory"
    generated_advice: "allow"
    profile_memory_budget_bytes: 16777216
    rules:
        parser_symbols:
            match:
                site_label: "parser.symbols"
            hints:
                lifecycle: "build_then_read"
                lookup: "heavy"
                update: "rare"
            objective: "compact"
            switching: "boundary"
```

A second file can include the first. Relative paths resolve against the including file. Include handling must enforce cycle detection, bounded depth/files/bytes, duplicate identity handling, and configured path roots. Required missing files fail; explicitly optional generated files produce a visible “no advice loaded” state. No shell evaluation, network fetch, or arbitrary environment substitution is implied.

Resolve the include graph once before planning and publish an immutable policy snapshot. Store all content digests in dependency metadata. Reusing the shared SDN parser does not imply the composition behavior already exists. [R14]

*Review 2026-11-06:* `simple.collection-policy.v1` is not a second schema with its own loader. It is the `rules.<name>` collection row of the data plan's `simple.data-policy/v1` envelope (data plan §8.3) and is loaded, digested and explained by that plan's W1 resolver; `ResolvedCollectionPolicyV1` is the typed result of that row. Include handling is the resolver's, not a collection-only feature.

### 5.3 Precedence is not one last-writer-wins list

**Hard requirements intersect.** ABI/ownership/assurance constraints, existing semantic guarantees, and explicit physical pins must all hold. A conflict is an error, not a winner chosen by source order. A profile never defeats a source layout pin or a critical-mode allocation prohibition.

For **soft hints and preferences**, use a separate deterministic precedence:

```text
explicit local source hint
  > explicit exact-site project/user rule
  > named source-selected policy
  > explicit module/project defaults
  > accepted generated advice
  > compiler heuristic default
```

A project can forbid selected representations globally as a hard policy. Two same-rank explicit rules for the same field are errors unless an explicit override relationship is declared. Include order alone must not quietly reverse equally specific rules.

Within SDN, exact site identity is more specific than a qualified symbol selector, which is more specific than a module pattern. Report both the chosen value and its provenance. “User preference” is not an escape hatch from language correctness.

### 5.4 Profile output and reproducibility

Keep three artifacts conceptually separate:

- **Observed evidence:** versioned `.sprof`, including sampling provenance and missingness.
- **Derived advice:** generated SDN with workload hints, confidence, and evidence digests.
- **Selected plan:** a deterministic plan receipt/lock manifest with implementation, layout, target, and cost-model identities.

Never overwrite hand-authored source or project policy during a profile run. Export advice to a generated file; applying a pin is a deliberate developer action. For reproducible release builds, use reviewed advice plus a frozen plan receipt. Missing or stale mandatory inputs fail the reproducibility gate; advisory builds may fall back visibly.

---

## 6. Improved architecture and ownership

```text
Source literals, APIs, local attributes        SDN include DAG
                  |                                  |
                  +---- typed-HIR facts + policy -----+
                                      |
                             logical CollectionPlan
                                      |
               shared MIR PerfFacts / ownership / effects
                                      |
           immutable ProfileSessionView + target capabilities
                                      |
                        bounded physical-plan search
                                      |
                       PhysicalCollectionPlanV1
                 /             |              \
       primary + indexes   StorageLayoutPlanV1   execution/residency
                 \             |              /
                      verified lowering / kernels
                                      |
                       runtime transition controller
                       (only for admitted live plans)

Region timings ----\
CPU samples --------+
Native counters ----+--> one session/identity/codec/query model
Collection counts --+             |
Alloc/COW data -----+       perf reports + PGO + JIT + IDE
Field/device data --/
```

### 6.1 Contracts to add, owners to retain

| Contract/component | Responsibility | Integration owner |
|---|---|---|
| `CollectionSemanticContractV1` | Family, order, equality/hash, mutability, reference/index behavior, complexity promises | Shared collection operation/type contracts; not backend-local |
| `CollectionOriginV1` | Source creation origin, generic specialization, operation sites, lineage | Existing typed-HIR performance collector and revision identities |
| `ResolvedCollectionPolicyV1` | Normalize local attributes and SDN, provenance, constraints | Compiler policy layer using shared SDN infrastructure |
| `CollectionProfileV1` and query view | Typed measurements, sampling metadata, confidence/missingness | The existing `sprof-v2` collection envelope (`src/app/optimize/sprof_collection_profile.spl`) plus the data plan's W5 record families; a typed query view factored below `app.optimize` |
| `PhysicalCollectionPlanV1` | Primary storage, indexes, layout reference, dispatch, transitions, cost evidence | Existing `src/compiler/60.mir_opt/mir_opt/collection_plan_selection.spl` (MIR side) over `src/compiler/35.semantics/perf/collection_plan_selection.spl` (semantic side); no new directory |
| Existing `StorageLayoutPlanV1` | Logical record layout and conversion policy | Existing `common/structural/storage_layout` owner, unchanged V1 [R8] |
| `CollectionTransitionReceiptV1` | Generation, source/destination identity, ownership, bounds, completion | Runtime owner under compiler-approved transition contract |
| Existing optimizer registry | Scheduling and activation of transforms | `optimizer_plugin.spl` [R6] |

The shared profile schema/query records must be usable without importing `app.optimize` into compiler core. App-level loading, file I/O, export, and CLI remain adapters. Keep runtime data-plane records below the compiler; a generated program must not link the whole optimizer just to count operations.

### 6.2 Physical plan is a product, not a single enum

```text
PhysicalCollectionPlanV1
  semantic_contract_digest
  primary_storage
  indexes[]
  storage_layout_plan: StorageLayoutPlanV1
  memory_space_and_residency
  dispatch_strategy
  admitted_transitions[]
  ownership_and_backend_evidence_refs
  steady_memory_estimate
  peak_memory_estimate
  build_and_operation_costs
  profile_confidence
  fallback_plan_ref
  complete_plan_digest
```

A packed sequence can have a side hash index. A map can have packed SoA values and a separate lookup index. A key-frozen map can update values. A GPU-friendly read view can coexist with a host representation under an explicit version/lease rule. These are combinations of choices, not new semantic types.

Avoid the full Cartesian product of all candidates. Use legality pruning, backend capability pruning, then a bounded beam/Pareto search under compile-time budgets. Emit a reason when search stops early. Evaluate layout and kernel costs together rather than greedily selecting a layout first.

### 6.3 Plugin boundaries

Core owns semantic validity, the policy resolver, fallback contracts, identity, and transition admission. Optional providers supply candidate representations, cost functions, conversions, and kernels. Use existing plugin identity/version/selection mechanisms. No provider may claim unsupported field widths, safe aliasing, or a device completion fence that does not exist.

Prefer static specialization and dead-code elimination for ordinary applications. Do not make every lookup call a dynamic plugin. Select a kernel once per operation batch or use a small admitted representation tag only where live switching is actually enabled. Provider code, maps and dispatch tables are resident until process exit (XRay doc §C, data plan §1.3): releasing a profile session or a plan generation never unloads code, so no unload-wait protocol is designed here.

---

## 7. How perf profiling and collection profiling cooperate

**Yes: they should cooperate through shared identity, recording policy, storage, and reporting—not by routing every event through the same expensive function.**

| Existing/extended producer | Best question answered | Join keys | Must not be inferred |
|---|---|---|---|
| Region timer | Which stage/operation region consumes elapsed time? | Run, subject, task/thread, region, time range | Exact lookup counts or exclusive collection time from an inclusive region |
| CPU sampling/PMU adapter | Where execution or memory stalls concentrate | Build, native PC/source map, thread, interval | Unexecuted paths or exact coverage from absent samples |
| Function/block/edge counters | Which control-flow paths run and how often | Build, function/block/edge IDs | Container size or semantic mutation count without instrumentation |
| Collection collector | How this logical collection is used | Origin, instance sample, operation, phase, size class | Nanoseconds per operation from counts alone |
| Allocation/COW collector | Which storage generations allocate, copy, retain, or detach | Storage/generation, logical origin, allocation site | Unique ownership solely from an observed lack of copies |
| Field/loop collector | Which fields are used together and in which traversal | Origin, loop/kernel, schema field IDs, executed trip count | Disjointness solely from field names or co-access statistics |
| Device collector | Launch, transfer, execution, and wait cost | Submission/queue, device clock domain, plan generation | End-to-end speedup from kernel time alone |

Clang's distinction between sampling and instrumentation provides the relevant precedent: shared optimization use does not make the record types interchangeable. [P9]

### 7.1 A concrete correlated report

Illustrative output, not measured Simple performance:

```text
site: parser.symbols
subject: compiled-program        workload: large-source-files
region: parse.resolve            region time: inclusive, measured separately
lookup: 12,000,000 hits / 2,000,000 misses
successful key insertions: 120,000
key removals: 0 observed          value replacements: 900,000
lookup-weighted size p95: bucket [128, 255]
COW detach bytes: separately attributed
profile interpretation: key-build/read-heavy; values remain dynamic
candidate: packed entries + exact flat index
not authorized: immutable-key specialization without contract or guarded fallback
```

The profiler should explain whether the bottleneck is string hashing, the index, allocation/COW, or field scanning. A high lookup count alone does not identify the dominant time consumer.

### 7.2 Compiler self-profiling versus program profiling

A Simple compiler can itself contain hot collections, while the compiled program has different collection origins. Put `subject_kind` and subject build identity in every session. Keep compiler-stage metrics separate from generated-program PGO. They can be presented together, but cannot be merged into one operation population. This matters because the current stage adapter and region profiler have different scopes and capabilities. [R3], [R4]

---

## 8. Identity, attribution, and profile stability

### 8.1 Required identities

```text
RunId / WorkloadId / SubjectBuildId / TargetFingerprint
ModuleRevision / FunctionOrigin / InlineContext
CollectionOriginId / CollectionOperationId
LogicalInstanceId (sampled only where needed)
StorageInstanceId / StorageGeneration
LoopOrKernelId / DeviceSubmissionId
ResolvedPolicyDigest / PhysicalPlanDigest
```

`CollectionOriginId` identifies the creation origin, not a pointer or line number. Use the compiler's existing semantic/module identity machinery, a creation-kind discriminator, and a stable AST origin. Generic specializations need a canonical type fingerprint; local module TypeIds are not durable cross-module identifiers. Inlined clones retain parent origin plus context where useful.

A structural hash does not magically survive arbitrary edits. Store a mapping sidecar and source fingerprint. Allow safe remapping only with explicit confidence rules; reject ambiguous remaps. An optional `@col_site` label is the most stable user-facing selector and must be namespace-unique. Line/column are display fields, not the primary identity.

### 8.2 Logical identity versus physical storage

A move preserves logical lineage. A semantic value copy creates a new logical value even when COW initially shares storage. Detachment creates a new storage generation. A physical migration changes storage generation and plan, but not the logical content or source creation origin.

Use this distinction to avoid counting COW sharing as zero allocation forever or treating a migration as a new user-level collection. Assign factory-created origins where creation occurs and optionally summarize caller contexts; do not collapse every caller into one misleading average when use distributions differ strongly.

### 8.3 Operation ownership

Instrument by resolved semantic operation ID, not spelling such as `contains`. Built-in Dict, generic Map, text HashMap, and synthesized indexes can share semantic contracts without pretending they have identical physical costs. Instrument indexed reads/writes and compiler-lowered operations too; wrappers alone miss direct MIR accesses.

Keep user-visible semantic operations separate from implementation events such as probes, resize, rebuild, or internal reinsertion. A resize reinserting 1,000 entries is not 1,000 user insertions. Record it as maintenance work. Fusion and duplicated/inlined code retain origin maps so reports can explain executed physical work without double-counting one source operation.

---

## 9. Collection measurements: enough information to plan correctly

### 9.1 Core metric schema

| Metric family | Required distinctions | Collection policy affected |
|---|---|---|
| Creation/lifetime | Created, destroyed, still live at capture end, sampled population, caller context | Header overhead, conversion amortization, live memory |
| Cardinality | Current/max observed, capacity, cardinality-changing successes, growth/shrink events | Inline capacity, direct indexing, hash occupancy |
| Lookup | Hit/miss, equality/range/prefix/indexed access, operation-size distribution | Index type, negative-lookup path, scan/index tradeoff |
| Mutation | Insert attempts vs new keys; erase attempts vs success; value replace vs key mutation | Frozen-key eligibility, maintenance costs, churn |
| Traversal | Traversal starts, elements actually visited, early exits, field masks | Packed storage, SIMD, side indexes, fusion |
| Allocation/copy | Allocation bytes/count, reserved/live bytes, COW detach, rehash bytes | Memory objective, representation overhead |
| Key work | Key length distribution, hashed bytes, equality bytes where measurable, intern/cached-hash path | String-hashing cost, prefix indexes, reuse |
| Phase | Bounded operation windows, phase transitions, changes after long quiet periods | Safe-point opportunities, hysteresis |
| Layout access | Fields read/written together by loop, row vs column locality, actual trip counts | AoS/SoA/AoSoA/hot-cold choice |
| Device work | Residency, transfers, launches, waits, active-generation leases | GPU profitability and migration safety |

A successful replacement must not increment cardinality. A failed erase must not decrement it. Only committed mutations change the logical-state summary; exceptions/failures have separate outcomes. Track key-set changes independently of value changes.

### 9.2 Histograms need a defined population

Maintain distinct summaries when they matter:

- **Instance-weighted size:** distribution across created/completed instances.
- **Operation-weighted size:** size seen by lookup, update, or traversal operations.
- **Time-weighted occupancy:** space retained over time, using interval weights.

These are not interchangeable. A site may create many tiny maps but perform most work in a few large ones. At hot sites record bounded joint summaries such as `(operation kind, size bucket, phase, residency)`, rather than multiplying unrelated marginal averages.

Logarithmic buckets are inexpensive but coarse. A bucketed p95 should be reported as an interval, not as an invented precise size. Merge bucket counts or sketches, never average percentiles. Keep observed maximum distinct from a proven maximum bound.

### 9.3 Lifecycle detection without impossible look-ahead

Do not allocate “eight equal fractions of final lifetime” online: final lifetime is unknown. Use fixed operation-count windows, bounded recent-window rings, explicit application phases, and online change summaries. Normalize only after completion when sufficient data has been retained.

A collection alive at shutdown has a censored lifetime. Preserve that fact. No observed insertion after construction is evidence for a cost hypothesis, not permission to remove insert support. A phase detector may recommend freeze or a guarded plan; it cannot establish immutability.

### 9.4 Field access at loop granularity

Use static field masks plus actual executed loop/block counts where the mapping is sound. For conditionally executed field accesses, distinguish branches or sample the relevant blocks. Record co-access groups: separate counts for `x` and `y` do not say whether they are usually read together.

Do not increment a global counter for every field load. Enable detailed access tracing only for selected hot schemas/sites. Feed the resulting summaries to the existing storage planner through versioned cost/request metadata, not a second layout enum. LLAMA/AdePT is a useful precedent for combining these records with conventional device profiles. [P4]

---

## 10. Low-overhead collection instrumentation

### 10.1 Modes and explicit overhead contracts

| Mode | Data plane | Intended use |
|---|---|---|
| `off` | No collection probes, telemetry branches, telemetry header fields, TLS initialization, or telemetry dependencies in the target program | Normal builds; must be verified in generated code |
| `basic` | Direct per-thread/site counters and bounded size/growth summaries at selected sites | Training and coarse workload characterization |
| `sampled` | Sample instances or operation windows; retain inclusion probabilities and bounded metadata | Lower-overhead representative training |
| `deep` | Selected probe/latency/field/key-distribution records | Targeted diagnosis, not a default |
| `adaptive-runtime` | Budgeted online observations and safe-point checks | Explicitly opted-in live adaptation; not described as zero-cost when inactive |

“Disabled at runtime” is not the same as “compiled out.” Measure dispatch/adaptation overhead separately from profile overhead. An adaptive representation may still need a tag even with telemetry off; that is not profiling overhead and should not be hidden.

*Review 2026-11-06:* `off` is the static switch and is exactly `--xray` off / `trace.instrumentation: off` (byte-identical output, `check-xray-static-off-identity.shs`). `basic`, `sampled`, `deep` and `adaptive-runtime` are **runtime selections carried by aspect params** (`AspectParamsV1.ext["simple.trace/observer-v1"]`), not new SDN mode keys and not attributes; the native lane needs sleds to exist first, and the interpreter/JIT/Cranelift lanes reject `--xray` with `UnsupportedTarget`, where only the existing `collection_capture` counters remain.

### 10.2 Hot path

Compile a known site to a numeric slot and a cached per-thread counter-block pointer. Increment locally without a global lock, text key lookup, file I/O, or timestamp. Allocate/register blocks on a cold first-touch path under a budget; cache the result. Merge at thread/task boundaries or scheduled safe points.

Exact local counters still cost instructions and cache traffic. Saturate or flush safely; record saturation and dropped data rather than wrapping. Avoid cross-thread writes to per-instance statistics. For task migration or shared containers, attribute operations to the executing shard and reconcile lineage in a safe aggregation layer.

Instrumenting every application operation with the current region timer would perform clock reads and dictionary work. Keep that implementation for coarse regions, not collection micro-operations. [R3]

### 10.3 Sampling and memory bounds

Uniformly sampling instances at creation and observing selected lifetimes is often useful, but its estimates can have high variance when rare large instances dominate. Preserve inclusion probabilities and uncertainty; optionally stratify by observed size with a documented estimator. Sampling every fixed 256th operation can correlate with periodic workloads; use randomized or independently seeded windows for unbiased estimation when that matters.

Basic counters may be per-site rather than per-instance. Instance tracking belongs only to selected profiling modes and must not enlarge every production collection. A pointer-based side table is an alternative for escaped objects, but its lookup cost belongs in the overhead budget.

Memory must be budgeted globally, not just per record. For illustration, sixteen 64-bit counters already consume 128 bytes before histograms or descriptors; multiplying that by thousands of sites and many threads can be substantial. Use sparse active-site blocks, bounded per-thread pools, optional histogram blocks, and visible truncation. Do not let profiling allocate recursively through the collections it is profiling; use a noninstrumented recorder arena and a recursion guard.

### 10.4 Measuring instrumentation cost

Compare the same workload and compiler plan in three builds: baseline without probes, the same plan with probes, and optimized output with probes removed. Otherwise representation changes can conceal instrumentation overhead. Exact-counter builds validate accounting; sampled builds validate estimator accuracy against them. No fixed slowdown percentage is promised by this report.

---

## 11. `.sprof` evolution and data integrity

### 11.1 Reuse the planned versioned extension

*Review 2026-11-06:* the paragraph below is only partly true now. `sprof_loader.spl:190` accepts the `sprof-v2` version string and the collection-workload records are decoded by the sibling `sprof_collection_profile.spl`; the loader's **own** record validator still admits only function/block/edge (`:203`, `:339`, `:421`), so the paragraph remains true of that validator and false of the envelope as a whole. What is still missing is the field/node record families and a typed query view below `app.optimize` — the data plan's W5. The envelope sketch below is retained as the *target shape*; its name `ProfileSessionV2` is withdrawn because `sprof-v2` is already the shipped version string, and whether the additions are a v2 minor or `sprof-v3` is an owner question (data plan §17.5 Q1). Session identity fields (`run_id`, `subject_kind`, `workload_id`, …) are owned by `src/lib/common/trace/observer_session_v1.spl` and the loader's existing `run_id`/`workload_id`; they are referenced, not redefined.

The inspected v1 validators reject all kinds except function/block/edge. Both the app loader and native extraction helpers encode these assumptions. Add a version-aware shared schema/codec and adapters; do not smuggle collection metrics into function names or append unsupported records and call them compatible. The existing detailed plan already names an optional extended-profile codec. [R1], [R2], [R7]

Recommended envelope (target shape; name withdrawn, see above):

```text
ProfileSession (sprof-v2 envelope + W5 record families)
  schema_major / schema_minor
  run_id / subject_kind / subject_build_id
  workload_id / workload_weight
  target_fingerprint / backend_identity
  instrumentation_manifest_digest
  policy_and_plan_digests
  clock_domains_and_calibration
  sampling_description
  shards[]
  completeness_and_dropped_data

Typed optional record families:
  FunctionCounter / BlockCounter / EdgeCounter
  RegionTiming / CpuSample / Allocation / CowCopy
  CollectionSummary / CollectionSizeHistogram / CollectionPhaseWindow
  CollectionFieldSummary / DeviceExecution / CollectionTransition
```

Use explicit record kind/version/length and required-or-optional status in the new framing. Unknown required records fail; unknown optional records may be skipped by a v2-aware reader. A v1 reader is not thereby made v2-compatible. Continue reading valid v1 inputs, and offer an explicit v1 export of supported function/block/edge information where legacy consumers require it.

### 11.2 Summary sketch

```text
CollectionSummaryV1
  origin_id / type_fingerprint / context_id
  semantic_family / schema_digest
  instances_observed / instances_sampled / live_censored
  lookup_hit / lookup_miss
  insert_attempt / insert_new_key
  erase_attempt / erase_existing_key
  replace_value / mutate_key
  scan_start / scan_elements / indexed_read / indexed_write
  allocations / allocated_bytes / copied_bytes / retained_capacity
  size_summary_ref / operation_size_summary_ref / phase_summary_ref
  exactness / sample_weights / saturation / missing_fields
```

Make large histograms, field vectors, and temporal windows separate optional records. Do not multiply their memory by every site when the consumer needs only four counters.

### 11.3 Merge and trust rules

Deduplicate by run/shard/sequence, so reimporting the same file does not double counts. Merge raw compatible counts with saturation; preserve missingness rather than replacing missing fields with zero. Validate enum domains, lengths, arithmetic overflow, UTF-8, identities, and total input bounds. A partial crash flush is useful but explicitly incomplete.

Do not mix target-dependent timing curves from different devices as if identical. Operation distributions may be reusable across compatible targets while latency, transfer, and memory-alignment models remain target-specific. Preserve workload labels and explicit weighting; one unusually long test run must not silently define the production mix.

Profile data is untrusted optimizer input. It can change ranking among legal candidates but cannot authorize an unchecked pointer, missing bounds check, or absent fallback. Do not store plaintext keys, values, or source text by default; use schema/length/distribution statistics and local site metadata.

---

## 12. Physical candidates and cost model

### 12.1 Candidate families

| Semantic workload | Candidate representations | Main constraints |
|---|---|---|
| Tiny sequence/map/set | Inline packed storage; small flat lookup | Fixed header and reserved inline capacity can dominate; threshold must be measured |
| Dense bounded integer map | Direct-index values plus occupancy when needed | Checked range arithmetic; holes and out-of-range keys handled |
| Sparse integer/string equality map | Flat hash; packed records plus side index | Equality/hash contract, load factor, resize/maintenance cost |
| Ordered/range workload | Sorted flat representation; B-tree family | Preserve requested ordering and update behavior |
| Exact integer set | Small array, bitmap, chunked hybrid | Membership exactness; range/compression costs |
| Key-frozen lookup map | Sorted flat, frozen hash, MPHF plus exact validation | Key-set contract or correct guarded fallback; values may remain mutable |
| Rare updates with many reads | Mutable representation or frozen base plus bounded delta | Delta maintenance and merge costs; not V1 unless warranted |
| Bulk record traversal | Existing AoS/SoA/AoSoA or admitted grouped layout | Ownership, field width/schema, ABI, actual backend support |
| Large GPU-resident bulk work | Device view/index plus batch kernel | Residency, transfer, launch, synchronization, numerical/effect constraints |

Filter by semantics and backend evidence before using performance hints. For example, the existing layout heuristic can propose Grouped even while that physical mapping is documented incomplete; the combined planner must not lower an unavailable mapping. [R9], [R10]

*Review 2026-11-06:* of the rows above only the existing linear / chained-hash / AVL backends and one **sorted flat** candidate (C6) are scheduled. MPHF, frozen hash, bitmap/chunked hybrids, base-plus-delta and all GPU-resident rows are inventory; each needs its own measured proposal and none is a dependency of any C-package.

### 12.2 Time objective

For a candidate `p` and workload context `w`:

```text
T(p,w) = construction
       + sum_over_operations_and_size_buckets(count * calibrated_cost)
       + index_maintenance + resize_or_rebuild
       + dispatch + allocation_and_COW
       + conversion + transfer + launch + synchronization
       + deoptimization_or_fallback_cost
```

Separate successful/unsuccessful lookup, key hashing, equality, and probes when measurements support it. String costs depend on bytes, distribution, and cached-hash/interning behavior; `O(1)` index probes do not make fresh string hashing constant-time in string length. Integer mixing is bounded-width work, but adversarial distributions can still affect probing. These are different models, not interchangeable “hash lookup cost” constants.

Build once does not automatically favor an MPHF: construction must amortize across future queries. Rare updates do not automatically favor sorted storage: shifting cost and batch size matter. A useful index can be auxiliary rather than replacing the primary structure.

### 12.3 Explicit memory model

Let `N` be live entries, `C` allocated slots, `alpha=N/C`, `K` stored key bytes, `V` value bytes, `H` fixed header/descriptor bytes, and `P` bytes in external key arenas. These formulas are models, not measured Simple object sizes.

| Representation | Approximate model |
|---|---|
| Packed key/value array | `H + C*(K+V) + P` |
| Flat hash with one control byte/slot | `H + C*(K+V+1) + P + alignment/sentinel padding` |
| Packed entries plus 32-bit side-index slots | `H + N*(K+V) + Cindex*(4+1) + P`, while row IDs fit 32 bits |
| MPHF plus stored keys and values | `H + N*(K+V) + N*p/8 + P`, where `p` is MPHF metadata bits/key |
| MPHF with value only | `H + N*V + N*p/8`; valid as an exact dictionary only with an independently guaranteed known-key domain or other exact verification |
| Direct-index integer map over range `R` | `H + R*V + occupancy`, not merely `N*V` for a sparse range |
| Bitmap over range `R` | `H + ceil(R/8)` |

One-byte control metadata is grounded in the Swiss-table design; the load factor used below is an illustrative assumption. [P12]

For `u64 -> u64`, packed live payload is 16 bytes/entry. At `alpha=0.875`, the flat model is `17/0.875 = 19.43` bytes/entry, about 21.4% above that payload, **before** fixed headers and alignment. A packed-data/side-index model is `16 + 5/0.875 = 21.71` bytes/entry. Its extra bytes may be worthwhile for scan locality, but it is not automatically smaller. Immediately after growth, effective occupancy can be much lower than a maximum-load-factor calculation suggests.

For pooled strings, external bytes `P` are counted once; only descriptors/slots incur spare-capacity overhead. An MPHF's few bits/key are index metadata, not total exact string-dictionary storage. A short fingerprint is probabilistic and cannot silently replace key validation.

AoS and SoA do not inherently change useful field bytes. They change padding, descriptors, access locality, and sometimes temporary/live copies. Cost those separately.

### 12.4 Peak memory and switching break-even

```text
Peak = old live storage + new storage + scratch
     + retained indexes + device mirrors
     + unreclaimed generations + profile recorder memory
```

Track both host/device limits and simultaneous system residency. Include references that delay reclamation. Steady-state savings do not justify a transition whose peak violates the budget.

Switch only when a conservative savings estimate exceeds construction/conversion, migration, dispatch, and risk margin over the predicted reuse horizon. Illustrative arithmetic: if a conversion costs 0.4 ms and an independently measured saving is 20 ns per subsequent operation, simple break-even is 20,000 operations before safety margin. These numbers are not Simple measurements. Unknown remaining lifetime should reduce confidence or favor staying in the existing plan.

---

## 13. Switching modes: separate them explicitly

*Review 2026-11-06:* the authoritative application-mode table is the data plan's §11.1 (report only / next build / next instance / new snapshot / exclusive live switch / shared safe-point migration). The rows below map onto it: Static/AOT and Creation-time → next build / next instance; Growth and Phase/boundary transition → exclusive live switch; Online adaptation → exclusive live switch under §13.2 hysteresis; Temporary/cached view and JIT specialization are code or view changes, not storage application modes.

| Mode | Decision point | Runtime cost and guard |
|---|---|---|
| Static/AOT | Compile using policy, type facts, and training data | Can erase dispatch entirely; must remain correct for valid untrained inputs |
| Creation-time | Each new instance chooses from admitted implementations | One creation decision; normal growth/fallback still needed where required |
| Growth transition | Capacity/cardinality crosses a representation boundary | Bounded promotion, often easier to amortize with existing resize |
| Phase/boundary transition | Freeze, batch completion, epoch, or explicit safe point | Requires ownership/quiescence and migration receipt |
| Temporary/cached view | A kernel or region needs selected fields/layout | View lifetime, writeback, invalidation, and device fences |
| Online adaptation | Budgeted observations trigger a later boundary decision | Opt-in monitoring cost, hysteresis, cooldown, bounded transitions |
| JIT code specialization | Hot operation/kernel gets a specialized implementation | Representation-generation guard and real deoptimization/materialization evidence |

Do not equate changing code with changing storage. A new SIMD kernel may consume the same layout. A new layout may run on CPU. A GPU view may not replace the canonical host collection.

### 13.1 Correct fallback

A small map may promote when it grows. A direct-index map must handle a valid key outside its current interval by extending or falling back. A key-frozen representation needs either an enforced key-set contract, a supported structural-edit fallback, or explicit thaw semantics. A profile that saw no such operation is not sufficient.

Every fallback must preserve the original API's error and resource contract. Optional optimization failure can keep the old representation. A requested insertion into a bounded/no-allocation map may still fail under its existing semantics; adaptation must not silently introduce unbounded allocation to “fix” it.

### 13.2 Hysteresis

Require minimum evidence, a conservative projected gain, a minimum dwell period, a migration-byte/latency budget, and a cap on transitions. Use different promotion/demotion thresholds. Track prediction error after a switch; stop adapting when overhead or prediction error exceeds policy. Do not repeatedly turn a map into sorted storage and back as a bursty workload changes.

Runtime reevaluation consumes already loaded policy and compact measurements. It must not reopen SDN, scan the repository, invoke a shell, or run full research/planning on a lookup path. This continues the existing `.sprof` hot-path policy. [R1]

---

## 14. Migration protocol and semantic safety

### 14.1 Initial implementation: exclusive, bounded transitions

Start with exclusive-owner or quiescent transitions. Do not begin with lock-free concurrent migration.

```text
Active(generation g, plan A)
  -> admit transition: ownership, leases, backend, capacity, policy
  -> acquire exclusive state or immutable snapshot of g
  -> allocate/build B under the peak-memory budget
  -> validate B and preserved logical/index invariants
  -> publish generation g+1 at the agreed safe point
  -> release/retire A only after all admitted readers/device users finish
```

Building from an immutable snapshot requires a version check before publication; failure means discard/retry within a bounded policy, not merge arbitrary concurrent edits without a protocol. Holding exclusive ownership through conversion is simpler and may be the correct first implementation.

Publication is the representation linearization point, not a user-level mutation. Allocation failure, cancellation, validation failure, or lost exclusivity leaves the old active state usable. Partially built state never becomes visible.

### 14.2 Borrowing, identity, and COW

Do not silently reinterpret existing `&T` values as layout-independent proxy references. An escaping/raw/address-observing borrow pins the relevant representation or blocks migration until its lifetime ends. Explicit logical view APIs can be added only with their own contracts.

Iterators and indexes must obey existing invalidation guarantees. A migration must wait for leases, preserve the old generation, or provide a verified index translation where that is already legal. It may not add surprise invalidation to a live collection that formerly promised stability.

COW aliases must not observe another logical value's mutation. Read-only derived views may share immutable storage; value mutation detaches or invalidates views through the owning value's rules. A view key needs source storage generation, logical schema, layout plan, relevant field versions, and device identity. A layout hash alone is not enough.

### 14.3 Key and callback behavior

Preserve equality and hash semantics, duplicate resolution, insertion/key order where promised, range comparator behavior, and signed-zero/NaN policy. If hashing or equality can execute observable user code, a planner cannot freely add calls while building a new index. Require purity/effect evidence or preserve observable behavior. The same applies to allocation failure, exceptions, destructor timing, and reference-count behavior where exposed.

Stable row IDs should be distinct from physical offsets when indexes or handles outlive compaction. If a plan uses slot positions, its update/compaction code must update all dependent indexes atomically. Prefer a narrow exact set of supported operations over optimistic generality.

### 14.4 ABI and external boundaries

FFI, MMIO, wire formats, DMA, shared-memory ABI, and explicit raw pointers are hard constraints. `@layout(soa)` cannot override a C-ABI AoS record pin. Convert at an explicit boundary when permitted, or reject the request. Never label an ordinary tagged RuntimeValue array as owned raw typed storage to bypass the existing admission path. [R8], [R9], [R10]

Serialization and debugger inspection should expose logical content independent of the physical plan, while providing an explicit diagnostic view of physical layout. Raw byte serialization of a pinned type remains pinned.

---

## 15. SIMD, GPU, and existing layout integration

### 15.1 Reuse, do not restart

Keep `StorageLayoutPlanV1` unchanged. A collection plan supplies the logical storage/schema, proven access properties, policy digest, and target context through an adapter. If the existing request lacks new measured fields, create a versioned request/context wrapper, not an incompatible extension of frozen serialized V1.

The current owner records custom-native x86_64 admission for a narrow typed-storage path, with other widths/backends and general public-array integration still gated. Begin there and mark all other combinations explicitly unavailable. The current heuristic's `simd_width` or `gpu_bulk_fields` must not be treated as proof of SIMD correctness or GPU availability. [R9], [R10]

### 15.2 Batch plan selection

Bulk operations retain high-level semantic structure until fusion, dependence, and layout decisions are made. Select scalar, SIMD, threaded CPU, or GPU based on the complete pipeline and residency. A one-off lookup should not launch a GPU kernel merely because the collection is large.

Include transfer bytes, kernel launch, synchronization, selected-field packing/writeback, code generation, and cache reuse. Favor persistent device residency for repeated eligible operations. Use the existing host/device scheduling interfaces; collection planning should not invent a second GPU scheduler or driver layer.

### 15.3 Numerical and effect contracts

Elementwise transforms require absence of conflicting dependencies; reductions also require an explicitly permitted association/order policy. Deterministic floating-point results must not be changed by an automatic parallel reduction. Precision reduction is a separate opt-in numerical transformation, never an incidental layout optimization. Pointer-containing or dynamically shaped records require explicit supported codecs/projections, not raw copying of host object graphs.

### 15.4 Coherence

Maintain one authoritative writer per admitted mutable region or a stronger verified concurrency protocol. GPU completion fences control when buffers can be read, reused, retired, or unloaded. Record producer/consumer generations and dirty-field subsets. A host timestamp is not a device completion proof; device timing also needs a clock-domain mapping before it is placed on a shared timeline.

Phase-local selected-field views can reduce conversion volume compared with rebuilding the whole record store. That follows the annotation-guided data-view research, while Simple's decision to create the view remains separately costed and safety-checked. [P5]

---

## 16. Examples of end-to-end decisions

All examples are design scenarios, not benchmark results.

### A. Compiler symbol lookup with mutable values

```simple
@col(auto, lookup_heavy, build_then_read)
@col_site("compiler.resolve.symbols")
var symbols: {text: Symbol} = {}
```

The profile distinguishes key insertion, value replacement, hashed bytes, and lookups. If key membership is verified frozen after a phase, a compact exact frozen index may be legal while symbol metadata remains mutable. Without that proof, retain a dynamic map or an admitted structural-edit fallback. Interned IDs may eliminate repeated string work downstream, but caching a hash alone does not eliminate exact equality checks.

### B. Particle update and occasional UI inspection

```simple
@col(auto, scan_heavy, switch_at_boundary)
@col_site("simulation.particles")
var particles: [Particle] = []
```

Joint loop/field profiles indicate heavy position/velocity access and occasional name/metadata access. Compare existing AoS, admitted AoSoA, and field-group views. Preserve ordinary row access. Use GPU only when the whole pipeline, data availability, and device residency amortize conversion and transfers. A C interface taking `Particle*` either pins AoS or uses an explicit conversion boundary.

### C. Dense IDs that become sparse

A `Set<u32>` profile suggests a bitmap. The planner chooses a guarded range or chunked hybrid, not an unchecked array indexed by an assumed maximum. A later valid outlier triggers a supported representation/policy response. Train on outliers in the holdout tests.

### D. Millions of tiny collections

Header and sampling metadata can dominate useful payload. Prefer static or creation-time inline representations, and disable per-instance telemetry in the normal binary. The threshold is selected using full allocated-byte measurements, not only big-O or a folklore “eight elements” rule.

### E. Read-mostly sequence with searches and duplicates

The sequence remains ordered and duplicate-preserving. A side index maps keys to row IDs or row lists. Index maintenance and callback purity are included in its plan. This is not a legal place to substitute an ordinary unordered set.

---

## 17. Implementation plan and parallel work packages

Paths below are existing integration roots or proposed modules placed under the earlier plan's owners. Perform a collision census before adding a file; reuse any subsequently landed equivalent. Keep shared contract changes serialized under one integration owner.

| Package | Work and owner | Depends on | Acceptance evidence |
|---|---|---|---|
| **C0: authority and parity census** | Pin supported APIs, literal semantics, attributes, existing container families, profile producers, and layout/backend status. Integration owner. | None | Source inventory, semantic contract matrix, explicit supported/blocked routes; no transformation enabled. |
| **C1: collection contracts and origins** | Extend typed-HIR operation registry and origin lineage; map builtins and generic Map without spelling-based guesses. HIR/perf owner. | C0 | Stable IDs across harmless edits, rejection of ambiguous remaps, generic/caller context tests, operation accounting oracle. |
| **C2: local attributes + SDN** | Implement local binding retention, tag validation, named policies, deterministic includes, provenance, and constraints. Frontend/config owners. | C0–C1 | Source and SDN equivalents produce identical resolved policies; hard-conflict and include-cycle failures; seed/self-host parser tests. |
| **C3: shared profile schema/adapters** | Add versioned records/query view below app I/O; retain v1 reader and native/JIT/report adapters. Profile owner. | C1 | Old fixtures read unchanged; v2 roundtrip, unknown-required rejection, optional skipping, dedup, saturation, corruption limits. |
| **C4: instrumentation** | Numeric site counters, sampled instances/windows, allocation/COW correlation, compiled-out mode. MIR/runtime owners. | C1,C3 | Exact synthetic traces match oracle; sampled estimates tested; off-build probes/dependencies absent; memory bounded. |
| **C5: report-only planner** | Histograms/phase analysis, calibrated cost table, explain output, generated advice. Existing CollectionPlan owner. | C2–C4 | Recommendations carry evidence/confidence, unknowns preserved, no semantic rewrite, heldout workload evaluation. |
| **C6: scalar specialization** | Admit compact/flat/direct-index/sorted candidates and existing generic interfaces; static and creation decisions first. Collection/runtime owner. | C5 | Differential operation traces and backend parity; no unexpected dispatch for static plan; measured build/lookup/scan/memory curves. |
| **C7: guarded switching** | Growth promotion, exclusive boundary migration, receipts, rollback, COW/iterator/borrow gates, hysteresis. Ownership/runtime owner. | C6 | Fault injection, stale-generation rejection, alias tests, valid outlier fallback, no lost entries, bounded peak memory. |
| **C8: layout integration** | Feed existing StorageLayoutPlan and typed-view admission; integrate logical field accesses and view versions. Existing storage-layout owner. | C2,C5 and existing typed-storage gates | Independent logical oracle plus conversion tests; admitted width/backend only; address pinning and cache identity verification. |
| **C9: SIMD and device execution — BLOCKED (review 2026-11-06)** | Not part of this program. GPU/device execution needs its own plan with real device evidence; nothing in C0–C8 or W0–W10 depends on it. | — | None scheduled. |
| **C10: online adaptation/advanced candidates (deferred)** | Limited phase adaptation only; base-plus-delta, chunk-local optimization and recursive-layout research are inventory. | C7, and the data plan's W9 shared-migration contract | No oscillation regressions; bounded compile/runtime search; representative gains with a working disable/fallback path. |

**Local attributes are in C2, not deferred until C10.** Profiling and explain-only planning are valuable deliverables before storage migration is enabled. A set-literal additive parser lane can run with C2, but should not block profiling existing arrays and dictionaries.

### Integration mapping

- Extend the landed `src/compiler/35.semantics/perf/collection_plan_extractor.spl` collector and `config/compiler/collection_operations.sdn` (currently an empty `pending-admission-v1` snapshot that admits no operations; C1 fills it). There is no `20.hir/perf`.
- Keep effect and alias knowledge with existing common effects, `55.borrow`, and shared MIR `PerfFacts` (`src/compiler/60.mir_opt/mir_opt/perf_facts.spl`).
- Place new physical planning in the existing `src/compiler/60.mir_opt/mir_opt/collection_plan_selection.spl` / `collection_plan_explain.spl`; do not create a `60.mir_opt/collection_plan/` directory.
- Reuse `60.mir_opt/optimizer_plugin.spl` for selection/activation and structured remarks.
- Keep file operations in `app/optimize`; factor reusable profile DTO/codec/query parts below app-only dependencies.
- Feed `95.interp/execution/sprof_hotspot_bridge.spl` through explicit typed adapters, not a new collection-only JIT.
- Reuse `common/structural/storage_layout` and compiler typed-view ownership; do not create a parallel SoA implementation.
- Keep profile record writing and recorder allocation independent of profiled collections to avoid recursion.

These integration choices extend already documented ownership boundaries. [R5], [R6], [R7], [R8], [R9], [R10]

---

## 18. Verification and benchmark plan

### 18.1 Correctness matrix

| Test group | Required cases |
|---|---|
| Literal/attribute parity | Existing empty Dict; new nonempty Set; contextual empty Set; nested/spread/comprehension errors; same AST semantics across seed/self-host/formatter/IDE; local attribute preservation |
| Policy | Source/SDN equivalence; include DAG/cycles/missing files; same-rank ambiguity; hard constraint conflicts; optional advice missing; per-field provenance |
| Accounting | Duplicate insert, failed erase, value update, key mutation, early-exit scan, thrown callback, resize reinsert, COW detach, moved/copied collection, shared/thread-migrated collection |
| Profile integrity | v1 compatibility, v2 forward rules, truncated files, oversized counts/lengths, saturation, duplicate imports, target mismatch, stale IDs, partial/censored capture |
| Container semantics | Randomized trace differential against independent model; collisions and adversarial keys; negative/outlier integers; variable strings; duplicates/order; custom effects |
| Switching | Every admitted source/destination pair; forced allocation failure; cancellation; active borrow/iterator; shared COW; version change during prepare; rollback and reclamation |
| Layout | Independent logical field oracle, not only roundtrip; alignment/overflow/bounds; unsupported field widths; ABI pin; field writeback and dirty versions |
| Device | Real execution, all leases/fences, device lost/cancel, host read after kernel, source mutation invalidation, mirror budget, no premature free/unload |
| Compiler/JIT | Wrong/stale profile cannot change results; representation guards; deopt materialization; cache key includes policies/plans/providers; activated pass witnesses |

A conversion and its inverse can share the same bug, so roundtrip alone is insufficient. Compare logical contents and operation outcomes with an independent reference implementation.

### 18.2 Performance matrix

Vary integer/string keys; tiny through large cardinalities; lookup/update ratios; hit/miss ratios; fresh versus cached hashes; common-prefix strings; dense/sparse/outlier integer ranges; append-only/churn/burst phases; scan-heavy/lookup-heavy mixes; all-fields versus selected-fields access; COW sharing; host/device residency; and actual target SIMD support.

Measure construction, steady lookup/update/scan, iteration order costs, rehash, conversion, fallback, startup, code size, allocation count, retained capacity, maximum host/device memory, and total end-to-end execution. Include the cost of collecting a profile separately from the optimized program.

Use repeated and interleaved baseline/candidate runs with identical logical inputs and documented warm/cold conditions. Report distributions and uncertainty, not only a single best run. Compare heldout workloads and adversarial phase changes. Do not generalize one CPU's threshold or one GPU kernel's timing to all targets.

### 18.3 Release gates

A physical candidate is enabled only after its semantics, backend lowering, failure behavior, and measured cost model have evidence. Each active transform requires a positive activation witness, a negative rejection witness, verified IR, and a fallback explanation. Label status explicitly: `Implemented`, `AnalysisOnly`, `Unsupported`, `Disabled`, or `Blocked`, as appropriate.

Normal builds must demonstrate that collection telemetry is compiled out, not merely disabled. Online adaptation must report its own monitoring and switching overhead. Targets lacking device access remain unverified/blocked, not “passed by simulation.” No promised speedup or universal memory percentage is part of this design.

---

## 19. Developer workflow and inspectability

The following CLI is a proposed extension to the existing perf/optimize tooling, not a claim about currently accepted options:

```text
simple perf record --collect=regions,collections,allocations --output=training.sprof -- <program arguments>
simple perf report training.sprof --group=collection-site
simple optimize --collection-plan --profile=training.sprof --config=project.sdn
simple optimize --collection-explain=parser.symbols
```

A plan explanation should contain semantic family, exact source/SDN origin, effective policy, profile population/coverage, admitted candidates, rejected candidates with reasons, predicted construction/operation/memory costs, selected plan, fallback, and actual lowering status. Never show “SoA selected” as “SoA executed” when typed-array admission is missing.

IDE display can show `col` capabilities and physical-plan remarks without forcing users to learn every implementation. Debugger views present logical values and an optional physical/generation panel. Test/CI records retain profile, advice, and plan digests so a regression can be reproduced.

Do not load SDN or profiles on each operation. Parse/load once, cache immutable summaries, and invalidate only when relevant source, schema, target, policy, provider, or profile identities change. This is consistent with the existing loader's hot-path restrictions. [R1]

---

## 20. Decisions, risks, and completion criteria

### Final decisions

| Decision | Resolution |
|---|---|
| Public name | `col<T>` as a short capability/alias; no reserved keyword |
| Literal forms | Preserve arrays/maps; add set syntax; keep legacy empty `{}` behavior without an explicit new expected type |
| Local attributes | Required early; same resolver as SDN; compile-time metadata, not decorators |
| Profiling | Shared sessions/identity/query/codec with multiple specialized collectors |
| Profile authority | Statistical cost evidence only; never ownership, immutability, or alias proof |
| Layout ownership | Existing frozen `StorageLayoutPlanV1` and typed-storage admission |
| Runtime switching | Opt-in, bounded, safe-point based, with generation and rollback contracts |
| Initial optimization | Static/creation-time specialization and report-only analysis before online adaptation |
| GPU | Batch/residency and real completion evidence; no automatic per-lookup offload |
| Reproducibility | Profile facts, generated advice, and selected plan receipts are separate versioned artifacts |

### Principal risks and controls

The largest correctness risks are silently changing empty-brace semantics, losing local attributes, treating profiles as proofs, changing exposed layout/reference behavior, and publishing a conversion before all consumers are safe. Control them with compatibility fixtures, one attribute/policy binder, proof-bearing admission, generation/lease protocols, and backend-specific activation gates.

The largest performance risks are telemetry on every field load, excessive per-instance metadata, incorrect workload weighting, sparse direct-index ranges, expensive MPHF construction on short-lived data, conversion thrashing, and repeated host/device transfers. Control them with bounded sampling, joint workload summaries, explicit peak-memory accounting, hysteresis, and transfer-inclusive measurement.

The largest architecture risk is duplication: a second collection profiler, a second layout enum, an app-importing compiler, a third operation-cost registry, or a GPU scheduler hidden in the collection library. Keep the ownership map in this report as a merge-review checklist.

**Completion means:** existing programs retain meaning; local attributes and SDN produce the same policy; perf and collection records correlate correctly; at least one useful static specialization and one bounded switch pass independent logical tests and measured cost evaluation; unsupported layout/device routes remain explicit. It does not require every research candidate to be implemented at once.

---

## 21. TDD and SSpec plan (reviewed 2026-11-06)

Authoring rules, lanes and the unified W/C dependency order are in the data plan §17.1, §17.2 and §17.4 and are not repeated. This section gives the C-package rows and maps the §18.1 correctness matrix onto spec files. Paths are canonical (`test/01_unit|02_integration|03_system`, never the `test/unit` shadow tree); no spec file is created by the review. RED-by-design specs carry `# @tag:in-development` on line 1 and `# Tracks: doc/03_plan/compiler/data/adaptive_collections_profiling_switching_2026-09-16.md §21 <Cn>` on line 2.

| Pkg | First failing spec (canonical path) | `describe` / first `it` | RED evidence expected | GREEN gate | Lane / tag |
|---|---|---|---|---|---|
| C0 | same file as W0: `test/01_unit/compiler/data/data_authority_census_spec.spl` (add the collection rows) | `it "pins AdaptiveMap's linear, hash and ordered backends and their 8/32 defaults"` (`# oracle: adaptive_text_set.spl:123-124`) | none — GREEN on first run | stays GREEN; a threshold change updates it in the same PR | interpreter / untagged |
| C1 | `test/01_unit/compiler/semantics/collection_origin_identity_spec.spl` (beside `aspect_join_point_spec.spl`) | `describe "Collection origin identity"` / `it "keeps the same origin id across a whitespace-only edit of the enclosing function"`; then `it "rejects an ambiguous remap instead of guessing"` | RED today: the `ast://…#source_hash` id changes on any source edit, so the harmless-edit `it` fails with two different ids | §18.1 "Literal/attribute parity" + §8.1 stability; `collection_operations.sdn` carries reviewed rows (no longer `pending-admission-v1`) | interpreter / in-development |
| C2 | `test/01_unit/compiler/frontend/collection_site_attribute_spec.spl` (beside `collection_feedback_state_take_install_spec.spl`); SDN side in the data plan's W1 `data_schema_resolver_spec.spl` plus `test/01_unit/compiler/config/collection_policy_includes_spec.spl` | `describe "Collection site attribute"` / `it "carries the site label from the declaration into HIR unchanged"`; `it "rejects an unknown collection tag instead of dropping it"`; includes spec: `it "fails on an include cycle and names the cycle"` | label absent from the HIR field record; unknown tag silently accepted; no include resolution | §18.1 "Policy" rows GREEN; source and SDN produce byte-identical `ResolvedCollectionPolicyV1` digests | interpreter / in-development |
| C3 | ≡ W5 `test/01_unit/app/optimize/sprof_data_observation_spec.spl` | `it "reads an old sprof-v1 fixture unchanged"` (GREEN today); `it "rejects an unknown required record kind and skips an unknown optional one"`; `it "does not double-count a re-imported shard"` | optional/required distinction missing — unknown kinds all reject; re-import doubles counts | §18.1 "Profile integrity" GREEN | interpreter / in-development (except the v1 fixture `it`) |
| C4 | `test/01_unit/lib/collections/collection_site_counters_spec.spl`; off-build proof through `scripts/check/check-xray-static-off-identity.shs` | `describe "Per-site collection counters"` / `it "matches an exact synthetic operation trace against the oracle"`; `it "records saturation instead of wrapping"` | counters are the text-keyed global `collection_capture` path; no numeric slot, no saturation flag | §18.1 "Accounting" GREEN; static-off native artifact byte-identical | interpreter + native build / in-development |
| C5 | extend existing `test/01_unit/compiler/mir_opt/collection_plan_explain_spec.spl` and `test/01_unit/app/optimize/collection_plan_cli_spec.spl` | `it "reports a recommendation with its evidence digest, coverage and confidence"`; `it "retains the original representation when the profile is stale"` | explain output has no evidence/confidence fields; stale profile is not rejected | report-only planner GREEN; no semantic rewrite in any `it` | interpreter / in-development for the new `it`s |
| C6 | `test/01_unit/lib/collections/sorted_array_backend_spec.spl` (beside `adaptive_set_loop_spec.spl`) | `describe "Sorted entry array backend"` / `it "answers the same lookups as the linear and hash backends on a randomized trace"` | backend missing | §18.1 "Container semantics" differential GREEN; memory/lookup curves recorded (§18.2) | interpreter / in-development |
| C7 | ≡ exclusive-owner subset of W9 `test/01_unit/lib/collections/representation_migration_spec.spl` | `it "promotes on growth without losing an entry under forced allocation failure"`; `it "refuses to migrate while a borrow is live"` | no receipt, no allocation-failure path, no borrow gate | §18.1 "Switching" GREEN for exclusive transitions; shared safe-point part stays W9 | interpreter / in-development |
| C8 | ≡ W7 (data plan §17.3) | — | — | — | native build (x86-64) |
| C9 | none — blocked | — | — | — | hardware; not scheduled |
| C10 | `test/01_unit/lib/collections/adaptation_hysteresis_spec.spl` | `it "does not oscillate between sorted and hash under a bursty trace"` | no hysteresis policy object | bounded transitions per policy | interpreter / in-development, deferred |

§18.1 matrix → files: Literal/attribute parity → C2 spec (set-literal rows dropped, see §3); Policy → W1 + C2; Accounting → C4; Profile integrity → C3; Container semantics → W4 adapter spec + C6; Switching → C7/W9; Layout → W7; Device → none (C9 blocked); Compiler/JIT → `test/01_unit/compiler/interpreter/sprof_hotspot_bridge_spec.spl` (existing) plus a cache-key `it` in W8's `data_policy_cache_identity_spec.spl`.

## Appendix A. Repository evidence references

All repository links below are pinned to the audited revision. Source excerpts were read through the GitHub connector. Status documentation is identified as documentation, not substituted for execution.

[R1]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/app/optimize/sprof_loader.spl
[R2]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/app/compile/native_profile_counter_runtime.spl
[R3]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler/90.tools/perf/profiler.spl
[R4]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler/85.mdsoc/adapters/in/profiler_adapter.spl
[R5]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler/95.interp/execution/sprof_hotspot_bridge.spl
[R6]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler/60.mir_opt/optimizer_plugin.spl
[R7]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/.spipe/simple_compiler_performance_memory_efficiency/design_lanes/detail_collection_memory.md
[R8]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/lib/common/structural/storage_layout/storage_layout_contracts.spl
[R9]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/lib/common/structural/storage_layout/planner.spl
[R10]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/doc/00_llm_process/feature_expert/storage_layout/skill.md
[R11]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/lib/nogc_sync_mut/src/map.spl
[R12]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler_rust/parser/src/expressions/primary/collections.rs
[R13]: https://github.com/ormastes/simple/blob/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/compiler/10.frontend/parser_extensions.spl
[R14]: https://github.com/ormastes/simple/tree/6a133cf2bd2589a6a62f6c83ec7f10f932084e64/src/lib/common/sdn

| Reference | Evidence used |
|---|---|
| [R1] | Loader lines 1–380: schema/version, records, hot-path restrictions, validation, merge, serialization |
| [R2] | Native helper lines 1–155: slots, counter kinds, extraction, serialization |
| [R3] | Profiler lines 1–190: clocks, text-keyed counters, reports, benchmark API |
| [R4] | Full short adapter: completed-stage count and last-stage implementation |
| [R5] | Bridge lines 1–140: primitive input/no app import, hotspot facts and source availability |
| [R6] | Descriptor definitions/factories lines 1–150: shared scope/application model |
| [R7] | Detailed design lines 1–230: proposed owners, facts, CollectionPlan, codecs, registry |
| [R8] | Frozen layout contract, enum, conversion policy, validation |
| [R9] | Complete layout request and deterministic heuristic |
| [R10] | Owner-maintained landed/incomplete list and typed-storage admission limits |
| [R11] | Generic Map lines 1–150: type parameters, Hash/Eq bounds, buckets, cached hash, insertion |
| [R12] | Parser lines 1–220 and 245–440: bracket/brace dispatch and dictionary parsing |
| [R13] | Attribute helper lines 1–155: argument vocabulary; not proof of complete local binding support |
| [R14] | Shared SDN source directory inventory; recursive include behavior not verified |

## Appendix B. Primary research and documentation

[P1]: https://programming-journal.org/2025/10/3/
[P2]: https://homes.cs.washington.edu/~mernst/pubs/generalized-synthesis-icse2018-abstract.html
[P3]: https://arxiv.org/abs/2106.04284
[P4]: https://arxiv.org/abs/2302.08252
[P5]: https://arxiv.org/html/2502.16517v1
[P6]: https://doc.pypy.org/interpreter-optimizations.html
[P7]: https://arxiv.org/abs/1603.06549
[P8]: https://developer.apple.com/documentation/swift/collection
[P8b]: https://developer.apple.com/documentation/swift/randomaccesscollection
[P8c]: https://github.com/swiftlang/swift/blob/main/stdlib/public/core/RandomAccessCollection.swift
[P9]: https://clang.llvm.org/docs/UsersManual.html#profile-guided-optimization
[P10]: https://futhark-lang.org/blog/2022-11-03-short-circuiting.html
[P11]: https://arxiv.org/abs/2605.01140
[P12]: https://abseil.io/about/design/swisstables

| Reference | Citation and relevance |
|---|---|
| [P1] | Makor, Kloibhofer, Hofer, Leopoldseder, Mössenböck. **Automated Profile-Guided Replacement of Data Structures to Reduce Memory Allocation.** The Art, Science, and Engineering of Programming, 2025, 10(1), article 3. Publication page/abstract reviewed. |
| [P2] | Loncaric, Ernst, Torlak. **Generalized Data Structure Synthesis.** ICSE 2018, pp. 958–968. Author publication page/abstract reviewed. |
| [P3] | Gruber et al. **LLAMA: The Low-Level Abstraction For Memory Access.** Software: Practice and Experience, 2022; arXiv:2106.04284. Abstract and publication metadata reviewed. |
| [P4] | Gruber, Amadio, Hageböck. **Challenges and opportunities integrating LLAMA into AdePT.** 2023, arXiv:2302.08252. Abstract reviewed. |
| [P5] | Radtke and Weinzierl. **Annotation-guided AoS-to-SoA conversions and GPU offloading with data views in C++.** 2025 extended version, arXiv:2502.16517v1. HTML text reviewed, including scope and annotation/view constraints. |
| [P6] | PyPy official documentation, **Standard Interpreter Optimizations**, dictionary/list strategies. Mechanism cited, not its historical benchmark percentages. |
| [P7] | Lemire, Ssi-Yan-Kai, Kaser. **Consistently faster and smaller compressed bitmaps with Roaring.** Software: Practice and Experience, 2016; arXiv:1603.06549. Abstract reviewed. |
| [P8], [P8b], [P8c] | Apple official Swift documentation and Swift's `RandomAccessCollection.swift` source, read 16 September 2026. Source confirms bidirectional refinement and constant-time offset/distance requirements. Capability model; not adaptive physical planning. |
| [P9] | Clang official **Profile Guided Optimization** documentation, especially differences between sampling and instrumentation. |
| [P10] | Philip Munksgaard, Futhark author explanation **Array short-circuiting**, 3 November 2022, linked to the SC22 work. Memory-dependence and intermediate-buffer reasoning. |
| [P11] | Singhal et al. **SoCal: A Language for Memory-Layout Factorization of Recursive Datatypes.** Submitted 1 May 2026, arXiv:2605.01140. Preprint; later-stage research relevance only. |
| [P12] | Abseil official **Swiss Tables Design Notes**. Control metadata design; example storage formulas in this report are explicitly modeled. |

**Evidence boundary:** the report is a design synthesis, not a systematic literature review, a performance measurement, or certification of Simple's current backend behavior. Unverified recursive SDN composition and incomplete public-array/device integrations are implementation gates, not assumed features.

## Repository cross-links

- Superseding integrated plan for data attributes, layouts, adaptive
  containers and XRay (2026-11-06):
  [`data_attributes_layout_containers_xray_2026-11-06.md`](data_attributes_layout_containers_xray_2026-11-06.md).
  Collection policy resolution reuses its shared SPL+SDN resolver (W1), and
  collection profiling reuses its versioned data-observation / `.sprof`
  extension (W5); no separate resolver or profile codec is introduced.
