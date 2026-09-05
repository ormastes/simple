# Semantic Incremental Build v2

## Tiered Local/Global Cache, Main-Branch Promotion, AOP-Aware Invalidation, Block Reuse, Storage GC, and Lean 4 Verification

**Status:** Proposed integrated architecture and parallel implementation plan
**Date:** 2026-08-09 (updated 2026-08-10)
**Relationship to the prior document:** Appends after Section 10 of
`doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md`.
It supersedes any wording that treats the cache as one undifferentiated store or AOP as one undifferentiated digest.

---

# 11. Executive decisions

1. **Use one semantic identity model across all tiers.** Local, machine-global, and remote-global caches use the same canonical `ActionDigest`, artifact digests, dependency fingerprints, AOP group digests, and block keys.

2. **Separate semantic identity from trust and Git history.** Branch name, Git commit, and CI workflow identity do **not** enter the semantic action key. They enter a separate admission and provenance record. This allows an unchanged action on a feature branch to hit a result produced on `main`.

3. **Use three persistent cache scopes, not merely "local" and "global."**
   - Workspace-local mutable query state.
   - Machine-global immutable CAS and per-user action indexes.
   - Remote-global CAS and trust-scoped action indexes.

4. **Developers read the remote-main cache but do not write it.** Only a trusted CI control plane may publish an action mapping into the main namespace. Content blobs may be uploaded earlier, but an unsigned or untrusted action-to-result mapping is never accepted as a main-cache entry.

5. **A remote branch result is promotable only after its exact source commit is reachable from an authenticated `origin/main` snapshot and its build provenance is valid.** A squash-merged or rebased-away branch commit is not directly promotable; the main commit must rebuild or reproduce the action.

6. **A cache hit is exact-key only.** Prefix, restore-key, nearest-branch, timestamp, filename, or "similar action" fallback is forbidden for compiler artifacts. Such fallbacks may be used only for explicitly non-semantic download caches.

7. **AOP uses layered cache groups.** Pointcut contracts, candidate indexes, per-target selections, weave plans, advice implementations, aspect packs, and runtime activation generations are distinct identities with distinct invalidation rules.

8. **Block-level reuse is an internal function optimization.** Persistent public dependencies stop at declaration/function boundaries. Basic blocks and regions may be cached for selected expensive passes, with stable semantic names and whole-function fallback.

9. **Storage management combines reachability and value.** Reachability from pins, active leases, retained action manifests, and release roots determines safety. LRU/age/recomputation cost only ranks safe-to-delete entries.

10. **Lean 4 verification is generated from the same cache schema used by the compiler.** The generator emits Simple data types and encoders, Lean models, theorem coverage obligations, and cross-language golden vectors. Durable safety proofs remain in separately maintained Lean modules and must contain no `sorry`, `admit`, or unreviewed axioms.

11. **Cache failure never changes program correctness.** A miss, full cache, unavailable remote service, or rejected upload falls back to computation. In mission-critical and release modes, any cache inconsistency causes quarantine and a strict recomputation; it never causes reuse of an uncertain artifact.

---

# 12. Repository baseline and gap analysis

The current tree already contains valuable foundations:

- `src/compiler/80.driver/driver_build/incremental.spl` persists file fingerprints, file dependency paths, and generated output paths. It also has an ad hoc symbol-level MIR cache under `.build/mir_cache/`.
- `src/compiler/80.driver/cache/cas_store.spl` implements a Phase-1 SHA-256 CAS and action manifest store with atomic rename and read-time digest verification.
- The existing CAS explicitly states that it is not wired into normal load paths and has no GC or remote cache.
- `doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md` already defines Option C: stamp-fast lookup backed by SHA-256 identity, with strict Option A verification.
- `src/verification/cache_identity/` already proves canonical-key field coverage, `no_false_hit`, AOP-field visibility, order independence, and the strict/fast bridge.
- The aspect-pack design already distinguishes static weaving, advice implementation, optional packs, catalogs, and session-local activation.

The required work is integration and refinement:

```text
current
    file dependency cache
    + standalone CAS
    + separate formal identity model
    + coarse AOP root
    + ad hoc per-function MIR files

target
    semantic query graph
    + tiered CAS/action stores
    + trusted main promotion
    + bounded GC/quota system
    + AOP group manifests and reverse indexes
    + selected block/region caches
    + generated Lean model and trace checker
```

Do not create a second CAS or a second action-key scheme. Evolve the existing Option-C types and make them the storage substrate for the semantic query architecture.

---

# 13. Research findings and design consequences

## 13.1 AOP and incremental weaving

| Research/result | Relevant finding | Simple design consequence |
|---|---|---|
| **Apostle: A Simple Incremental Weaver for a Dynamic Aspect Language** | Two dependency-table structures are sufficient for useful incremental reweaving, and work can be proportional to the program change. | Maintain explicit pointcut-to-candidate and target-to-selected-advice reverse indexes. Do not rediscover all relationships by scanning source on every build. |
| **AspectJ incremental weaving** | Per-class weaving permits local rebuilding, but a changed crosscutting specification can require rechecking every potentially affected class. Narrow pointcuts reduce the candidate universe. | Use per-target weave artifacts, bounded MDSOC candidate partitions, and public pointcut contracts. A broad root pointcut must deliberately pay a broad invalidation cost. |
| **Crosscutting/pointcut interfaces** | Explicit interfaces improve modularity by exposing stable crosscutting abstractions instead of coupling aspects to volatile implementation details. | A `pub pointcut` is both a language interface and an incremental-build boundary. Its contract, scope, exposed context, and selector schema form the public cache surface. |
| **AspectJ load-time weaving cache** | Woven bytecode can be cached and reused across later starts. | Cache static weave products as immutable artifacts, but never cache session runtime registries, loaded addresses, or mutable activation state globally. |

## 13.2 Incremental computation and build systems

| Research/result | Relevant finding | Simple design consequence |
|---|---|---|
| **Rust red/green query system** | Re-executing a dirty input does not need to invalidate consumers when the output fingerprint remains unchanged. Stable identities are required across sessions. | Apply red/green at module, declaration, function, AOP-selection, and selected block-analysis levels. Stop propagation when a semantic result remains equal. |
| **Nominal Adapton** | First-class stable names allow reuse across structurally changed executions; the formal model establishes from-scratch consistency. | Derive declaration and block identities from stable semantic anchors, not source lines, transient indexes, or heap addresses. Require a whole-function fallback when correspondence is ambiguous. |
| **Build Systems à la Carte** | Build systems can be decomposed into reusable components such as dependency discovery, scheduling, rebuilding, and caching. | Keep query evaluation, storage tiering, trust/admission, scheduling, and GC separate behind narrow interfaces. |
| **Bazel action cache and CAS** | The action cache maps exact action hashes to result metadata, while CAS stores content-addressed blobs; local and remote lookup can be layered. | Preserve the existing `/actions` and `/cas` conceptual split. Trust policy applies primarily to action mappings; CAS bytes are accepted only after digest verification. |
| **Nix GC roots** | Marking from explicit roots and deleting only unreachable store objects gives a principled safety model. | Pins, action manifests selected for retention, active leases, releases, and current bootstrap products are roots. LRU ranks only unprotected candidates. |
| **GitHub branch-scoped caches** | A branch can restore default-branch cache entries, while low-trust workflows receive read-only access to the default namespace; storage limits use age/LRU eviction. | Feature branches read trusted main entries. Main writes are CI-only. Branch entries are isolated and short-lived. |
| **SLSA cache-poisoning guidance** | A build cache should be keyed by the transitive closure of inputs and either be trusted-writer-only or carry verifiable provenance. | Require complete action keys plus trusted promotion receipts. Treat every restored file as untrusted until manifest, provenance, and content digests have been checked. |

---

# 14. Tiered cache architecture

## 14.1 Distinguish state, action mappings, and immutable content

The architecture has three different kinds of data:

```text
Workspace query state
    Mutable red/green graph, watcher generations, path receipts,
    local diagnostics, current branch/worktree state.

Action mapping
    ActionDigest -> ResultManifestDigest
    Scoped by repository and trust namespace.

CAS content
    ArtifactDigest -> immutable bytes
    Shared and deduplicated where policy permits.
```

Only immutable, canonically serialized values are globally shareable.

Never globalize:

- mutable interpreter globals,
- runtime AOP registries,
- JIT addresses,
- open file descriptors,
- loader generations,
- source watcher state,
- non-canonical absolute paths,
- unresolved negative lookups,
- random or time-dependent results,
- query results containing session-local IDs.

## 14.2 Cache tiers

```text
L0  Process cache
    Immutable in-memory values; single-flight per query/action key.

L1  Workspace-local cache
    .simple/build-cache/
    Mutable query DB + local action index.
    Accepts dirty worktrees and uncommitted edits.

L2  Machine-global cache
    $SIMPLE_CACHE/
    Shared immutable CAS across worktrees/clones.
    Per-user or per-trust-class action indexes.
    Never automatically promoted to remote main.

L3  Remote-main cache
    Shared remote CAS + repository/main action namespace.
    Readable by developers and CI.
    Writable only through trusted promotion.

L3b Remote-branch cache, optional
    Branch-identity namespace with short TTL and smaller quota.
    Writable only by the matching trusted branch CI policy.
    Never implicitly equivalent to main.
```

Recommended lookup order:

```text
process
→ workspace action index
→ machine action index
→ remote-main action index
→ matching remote-branch index, when policy permits
→ execute action
```

Remote main is queried before the branch namespace because it has higher trust. Since lookup is exact-key, a changed branch action naturally misses main and can then hit its branch namespace.

On a remote hit:

1. Fetch action mapping.
2. Validate namespace, schema, and exact `ActionDigest`.
3. Validate promotion/provenance policy.
4. Fetch the immutable result manifest.
5. Verify its digest.
6. Verify every referenced artifact digest while materializing it into the machine CAS.
7. Validate target, compiler schema, dependency interface roots, AOP roots, and block-manifest roots.
8. Publish a local action mapping only after the closure is complete.

## 14.3 Branch and commit must not pollute semantic identity

Do **not** add these to `ActionDigest`:

- branch name,
- commit SHA,
- pull-request number,
- CI run number,
- user name,
- workspace absolute path.

They reduce cache sharing without representing program semantics.

Instead, these fields belong in `PromotionReceipt`, `NamespacePolicy`, and GC metadata.

The semantic action key continues to include all actual build inputs:

```text
domain and schema
compiler executable and live compiler-source identity
target/backend/options
canonical source content
resolution receipt
dependency interface digests
macro root
AOP group/selection roots
declared compile-time environment
relevant block/region manifests when the action consumes them
```

Absolute source paths are normalized to repository/package-relative stable IDs before hashing.

## 14.4 Cache namespaces

```simple
enum CacheTrust:
    WorkspaceLocal
    MachineLocal
    TrustedBranchCi
    TrustedMainCi
    ReleasePinned

struct CacheNamespace:
    repository_id: Digest
    trust: CacheTrust
    target_profile: Digest
    schema_version: u32
    branch_identity: Digest?
```

Conceptual layout:

```text
<root>/
    cas/sha256/...
    manifests/sha256/...

    actions/
        workspace/<workspace-id>/sha256/...
        machine/<repo-id>/<user-or-trust-id>/sha256/...
        remote/<repo-id>/main/sha256/...
        remote/<repo-id>/branch/<branch-id>/sha256/...

    receipts/sha256/...
    metadata/
    leases/
    pins/
    tmp/
    trash/
    quarantine/
```

CAS blobs may be physically shared because every read verifies the digest. Action mappings are namespace-scoped because a correct content hash does not prove that a blob was produced by the claimed action.

For private repositories or mutually untrusted tenants, CAS storage must be tenant-scoped or encrypted even when action namespaces are separate, to avoid presence and content disclosure.

## 14.5 Result and promotion manifests

```simple
struct ResultManifest:
    action_digest: Digest
    result_kind: ResultKind
    artifact_digests: [Digest]
    output_fingerprint: Digest
    dependency_manifest: Digest
    aop_group_roots: [Digest]
    block_manifest_root: Digest?
    diagnostics_digest: Digest?
    producer_schema: u32

struct PromotionReceipt:
    repository_id: Digest
    source_commit: GitCommitId
    source_tree: GitTreeId
    trusted_ref: text
    trusted_ref_tip: GitCommitId
    clean_tree_digest: Digest
    action_digest: Digest
    result_manifest_digest: Digest
    builder_id: text
    workflow_digest: Digest
    toolchain_digest: Digest
    external_parameters_digest: Digest
    timestamp: Timestamp
    signature: Signature
```

The action index points to the result manifest and receipt:

```text
ActionDigest
    -> ResultManifestDigest
    -> PromotionReceiptDigest, for trusted namespaces
```

If the same `ActionDigest` is observed with two different result manifests:

- do not overwrite,
- quarantine both action mappings,
- emit a nondeterminism or poisoning diagnostic,
- force strict recomputation,
- fail mission-critical/release verification.

The CAS blobs themselves may coexist because their digests differ; the conflict is the action mapping.

---

# 15. Remote-main admission and branch promotion

## 15.1 Main eligibility

A result is eligible for the trusted remote-main action namespace only when all conditions hold:

```text
clean source tree
AND exact immutable source commit
AND authenticated repository identity
AND trusted origin/main snapshot
AND source commit reachable from that main snapshot
AND trusted CI builder and protected workflow
AND hermetic/declared action inputs
AND strict manifest and artifact verification
AND successful required tests/proofs
AND signed promotion receipt
```

The Git reachability check is conceptually:

```bash
git fetch --prune origin main
git merge-base --is-ancestor "$BUILD_COMMIT" refs/remotes/origin/main
```

The fetched remote identity, remote URL/repository ID, main tip, and fetch time are recorded. A developer-controlled stale local `origin/main` reference is not a trust proof.

## 15.2 Promotion modes

### Mode A — rebuild on main; default and mission-critical

```text
branch CI
    → optional branch namespace

main push/merge CI
    → build exact main commit
    → read main cache
    → optionally use branch blobs only as digest-verified candidate bytes
    → execute any missing/uncertain actions
    → publish signed main action mappings
```

This is the simplest trusted policy.

### Mode B — attested post-merge promotion; optional optimization

A trusted promotion job may relabel an existing branch result without re-executing it only when:

- the branch build was performed by an accepted trusted builder,
- the exact branch commit is now an ancestor of authenticated `origin/main`,
- source tree, action key, toolchain, workflow, and artifacts match the signed receipt,
- the action is deterministic and globally cacheable,
- no untrusted dependency or runtime state entered the result.

The promotion operation copies only action-mapping references. CAS blobs are already immutable and shared.

## 15.3 Merge strategy consequences

| Integration style | Branch tip reachable from main? | Direct promotion |
|---|---:|---|
| Fast-forward merge | Yes | Allowed with valid trusted receipt |
| Normal merge commit | Yes | Allowed with valid trusted receipt |
| Rebase then fast-forward | Only rebased commits | Old branch receipts not promoted |
| Squash merge | Usually no | Main must rebuild/reproduce |
| Cherry-pick | Original commit usually no | Main must rebuild/reproduce |
| Force-pushed main removing commit | No in new snapshot | Existing main entry may remain as immutable historical cache but cannot receive new promotion under that proof |

Source-equivalent squash results may still generate the same semantic `ActionDigest`. Main CI can then reproduce or strictly validate them and publish a new main receipt for the main commit.

## 15.4 Read and write policy

| Producer | Read remote main | Write remote branch | Write remote main |
|---|---:|---:|---:|
| Dirty developer worktree | Yes | No | No |
| Clean developer branch | Yes | No by default | No |
| Untrusted pull request/fork | Read-only, policy permitting | No | No |
| Trusted branch CI | Yes | Optional, isolated TTL namespace | No |
| Trusted main CI | Yes | Not needed | Yes |
| Release CI | Yes, strict verification | No | Yes + pin |

A local build remains successful if remote upload fails. Cache writes are best-effort. A release may fail only when required provenance or verification evidence cannot be persisted; ordinary cache capacity is not a correctness requirement.

---

# 16. AOP-aware cache groups and invalidation

## 16.1 Do not retain one opaque `AOP_selection_digest`

A single root digest is useful as a summary, but insufficient for precise invalidation. Split AOP identity into logical groups:

```text
AopSurfaceGroup
    Public pointcut/facet contracts and ownership scope.

AopCandidateGroup
    Candidate join-point descriptors partitioned by MDSOC scope,
    component, and join-point kind.

AopSelectionGroup
    One normalized pointcut plan evaluated against one or more
    candidate partitions; stores per-target ordered advice selections.

AopWeaveGroup
    Per-target weave plans and woven MIR/code artifacts.

AdviceInterfaceGroup
    Advice form, signature, effects/capabilities, ordering contract.

AdviceImplementationGroup
    Advice body and compiled artifact.

AspectPackGroup
    Physical deployment pack/catalog and member artifact references.

RuntimeActivationGeneration
    Loaded addresses, enabled bindings, active generation.
    Session-local only.
```

Logical invalidation groups are separate from physical storage packs. Small records may be packed together for I/O efficiency, but packing must not couple their cache validity.

## 16.2 Group keys

```simple
struct AopSurfaceKey:
    public_entity: EntityKey
    owner_scope: ScopeId
    visibility: Visibility
    exposed_context_schema: Digest
    assurance: AssuranceLevel

struct AopCandidatePartitionKey:
    component: ComponentId
    scope: ScopeId
    join_point_kind: JoinPointKind
    target_profile: Digest
    descriptor_schema: u32

struct AopSelectionKey:
    pointcut_surface_digest: Digest
    normalized_query_digest: Digest
    matcher_schema_digest: Digest
    visible_aspect_catalog_digest: Digest
    candidate_partition_roots: [Digest]
    advice_interface_root: Digest
    ordering_policy_digest: Digest

struct AopWeaveKey:
    target_preweave_mir: Digest
    target_join_point_descriptor: Digest
    selection_digest: Digest
    weave_mode: WeaveMode
    weaver_schema: u32
    backend_policy: Digest
```

For symbolic advice calls, `AdviceImplementationDigest` is intentionally not part of `AopWeaveKey`. It is consumed by link/load/activation actions.

For static inlining, `around` expansion, security-plan embedding, or specialization that copies advice body semantics into the target, the relevant advice implementation digest **must** enter the weave key.

## 16.3 Group manifests and Merkle partitioning

```simple
struct AopGroupManifest:
    group_id: Digest
    owner_scope: ScopeId
    generation: Digest
    pointcut_entries: [PointcutEntry]
    advice_interfaces: [AdviceInterfaceEntry]
    candidate_partition_roots: [Digest]
    selection_shards: [Digest]
    weave_artifacts: [Digest]
    implementation_artifacts: [Digest]
    aspect_pack_artifacts: [Digest]
    schema_version: u32
```

Candidate indexes are Merkle-partitioned:

```text
component
  └── MDSOC scope
      └── join-point kind
          └── stable entity-id range or prefix
              └── JoinPointDescriptor leaves
```

A new or changed candidate modifies only the leaf path and its partition root. Pointcuts read only the partitions permitted by their public scope.

## 16.4 Reverse dependency tables

Adopt the incremental-weaver lesson directly:

```text
pointcut group
    -> candidate partitions read

candidate descriptor field
    -> pointcut groups whose selector read-set uses that field

target entity
    -> current selection group and advice interface list

advice interface
    -> targets whose weave plan embeds or references it

advice implementation
    -> link/load/activation actions that consume it

aspect pack
    -> catalogs and deployment roots that reference it
```

Selector read sets distinguish fields such as:

```text
qualified name
owning scope
signature
attributes
effects
capabilities
type relations
call/execution kind
source annotations
```

Changing an attribute does not reevaluate a pointcut that uses only `within`, and changing a private body does not reevaluate a pointcut that sees only signature and attributes.

## 16.5 Invalidation transaction

When an AOP source changes:

1. Recompute the owning aspect/public-surface manifest.
2. Diff pointcut contracts, normalized queries, advice interfaces, advice bodies, priorities, and pack metadata.
3. Locate affected candidate partitions and reverse-index consumers.
4. Reevaluate only changed selection groups.
5. Diff old and new per-target ordered selections.
6. Reweave targets whose selection or embedded implementation changed.
7. Rebuild only advice implementation artifacts for body-only symbolic changes.
8. Relink or reload affected components/aspect packs.
9. Publish the new immutable group generation atomically.
10. Retire the previous generation only when no active runtime lease references it.

## 16.6 AOP invalidation matrix

| Change | Candidate index | Selection | Weave target | Advice artifact | Link/load |
|---|---:|---:|---:|---:|---:|
| Advice body, symbolic call | No | No | No | Yes | Yes |
| Advice body, statically embedded | No | No | Affected targets | Yes | Yes |
| Advice signature/form/effects | No | Affected pointcuts | Affected targets | Yes | Yes |
| Advice priority/order contract | No | Affected pointcuts | Targets whose order changed | Maybe | Yes |
| Pointcut query | Maybe new partitions | That pointcut | Selection delta targets | No | Yes |
| Pointcut public scope/visibility | Relevant partitions | That pointcut and importers | Selection delta targets | No | Yes |
| Target private body | No when descriptor unchanged | No | Recompile target body; preserve selection | No | Yes |
| Target signature/attribute/effect | One descriptor leaf | Pointcuts reading changed fields | If selection/descriptor changed | No | Yes |
| New matching public target | One leaf/path | Applicable pointcuts | New target | No | Yes |
| New imported aspect | Visible-aspect catalog root | Affected scopes | Selection delta targets | New advice | Yes |
| Runtime enable/disable | No | Precomputed plan unchanged | No static reweave | No | Session generation only |

## 16.7 Publicization and cache trust

- Publicized, scoped, deterministic AOP contracts are eligible for machine and remote caches.
- Same-scope private pointcuts may use workspace/machine cache when their complete scope index is represented.
- Legacy unpublicized cross-scope pointcuts use conservative scope/root invalidation in normal mode.
- Legacy unpublicized cross-scope pointcuts are errors in mission-critical mode and cannot be promoted to trusted remote main.
- Runtime-created pointcuts and mutable registries remain session-local unless they instantiate a predeclared deterministic public runtime surface.

A broad public root pointcut is cacheable only when its whole-root candidate index is part of the key. It is correct but intentionally expensive.

---

# 17. Block-level dependency tracking and reuse

## 17.1 Scope

Block-level caching is useful for expensive analyses and transformations inside large functions. It must not expose unstable CFG details as public cross-module dependencies.

Persistent public graph:

```text
module -> declaration -> function
```

Function-private subgraph:

```text
function -> region/SCC -> block -> semantic inputs
```

Consumers outside the function depend on the function interface, summary, or final artifact, never directly on a basic block.

## 17.2 Stable block identity

Never key by:

- source line,
- parser token offset alone,
- transient MIR block number,
- vector index,
- pointer/address,
- traversal order alone.

Use semantic anchors:

```simple
struct BlockKey:
    parent_function: EntityKey
    origin_anchor: StableAstId
    role: BlockRole
    structural_path: Digest
    same_anchor_ordinal: u32
```

Typical roles:

```text
Entry
Exit
IfCondition
IfThen
IfElse
LoopHeader
LoopBody
MatchArm
ExceptionHandler
Cleanup
ShortCircuitLeft
ShortCircuitRight
CompilerSynthesized
AopBefore
AopAfterSuccess
AopAfterError
AopAroundEntry
AopProceed
```

Compiler-synthesized post-weave blocks derive from:

```text
preweave BlockKey
+ WeavePlanDigest
+ advice slot
+ synthesized role
```

When matching old and new blocks is ambiguous, invalidate the parent function. A false miss is acceptable; a false hit is not.

## 17.3 Block query model

```simple
struct BlockInputFingerprint:
    canonical_mir: Digest
    predecessor_contracts: [Digest]
    successor_shape: Digest
    incoming_abstract_state: Digest
    semantic_read_set: [SemanticDependency]
    local_aop_plan: Digest?
    pass_schema: u32
    pass_options: Digest

struct BlockResult:
    transformed_block: Digest
    outgoing_abstract_state: Digest
    diagnostics: Digest
    local_summary: Digest
```

Queries:

```text
CanonicalizeBlock(function, block)
ComputeTransfer(pass, block, incoming_state)
OptimizeBlock(pass, block, incoming_state)
AnalyzeRegion(pass, region, entry_contract)
ComputeFunctionSummary(function, block_result_root)
```

## 17.4 Red/green dataflow propagation

For a forward analysis:

```text
in[b]  = join(out[p]) for predecessors p
out[b] = transfer[b](in[b])
```

Incremental algorithm:

1. Seed the worklist with changed blocks and blocks whose predecessor contract changed.
2. Recompute `in[b]`.
3. If block transfer inputs are unchanged, reuse `out[b]`.
4. Otherwise execute the transfer query.
5. Compare the new outgoing-state fingerprint with the old value.
6. If equal, mark the block green and stop propagation through that edge.
7. If different, enqueue successors.
8. For a loop, process the affected CFG SCC to a fixed point.
9. Compare final function summary with the prior summary; only propagate outside the function when it changed.

Backward analyses use successors analogously.

## 17.5 Pass eligibility

| Pass type | Initial granularity |
|---|---|
| Local constant folding / peephole | Block |
| Local liveness/gen-kill transfer | Block |
| Null/range/definite-init transfer | Block |
| Dataflow fixed point | Block worklist within function |
| Loop-specific optimization | Region or CFG SCC |
| Dominator construction | Function, with possible incremental research later |
| Inlining | Function/call-site |
| Escape/alias analysis | Function or call-graph SCC |
| Global value numbering | Function initially |
| Register allocation | Function initially |
| Machine block layout | Function initially |
| Final object emission | Function/codegen chunk initially |

Do not begin with independently relocatable machine-code blocks. First reuse canonical MIR, transfer results, diagnostics, and optimized region artifacts. Function-level codegen remains the safe initial emission boundary.

## 17.6 AOP interaction

AOP matching operates on stable pre-weave join-point descriptors.

```text
source/HIR anchor
    -> pre-weave JoinPointId
    -> target selection
    -> WeavePlanDigest
    -> derived post-weave block identities
```

Consequences:

- Advice-body-only symbolic changes do not rename target blocks.
- A selection change invalidates only blocks that contain affected join points plus any dataflow-reachable region within the function.
- If weaving changes exception edges, control flow, effects, or dominance globally, invalidate the required region or whole function.
- AOP-generated blocks include the pointcut/advice slot in their identity.
- Dynamic activation state never appears in persistent block keys.

## 17.7 Storage packing

Millions of tiny CAS files would create metadata and filesystem overhead. Store one `FunctionBlockManifest` and pack small block results into immutable chunks:

```simple
struct FunctionBlockManifest:
    function: EntityKey
    function_input_digest: Digest
    block_records: [BlockRecord]
    region_records: [RegionRecord]
    packed_chunk_digests: [Digest]
    large_block_digests: [Digest]
    merkle_root: Digest
```

Recommended physical policy:

- Small serialized block results are packed into indexed chunks.
- Large blocks/regions use separate CAS blobs.
- Logical block digests remain independent even when physically packed.
- GC marks a pack while any retained manifest references it.
- Background compaction may repack live small entries without changing logical digests.

Enable persistent block caching only when profiling predicts positive benefit, for example large functions or passes whose recomputation cost exceeds serialization and lookup cost.

---

# 18. Storage limits, cleanup, and garbage collection

## 18.1 Policy goals

The cache must:

- never fill the filesystem,
- never delete an artifact actively being consumed,
- preserve configured main/release/bootstrap roots,
- tolerate crashes during write or GC,
- repair metadata drift,
- degrade to a cache miss when capacity cannot be obtained,
- prevent a branch namespace from evicting all high-value main entries,
- expose why bytes remain protected.

## 18.2 Configurable limits

```sdn
cache:
    workspace:
        enabled: true
        max_bytes: "auto"

    machine:
        root: "$SIMPLE_CACHE"
        max_bytes: "auto"
        high_watermark: 0.90
        low_watermark: 0.75
        min_free_bytes: "auto"
        min_free_ratio: 0.05
        hard_limit_ratio: 1.05

    remote:
        endpoint: "..."
        read_main: true
        write_policy: "trusted_main_ci"
        branch_cache: "optional"
        branch_ttl_days: 7

    retention:
        main_generations: 8
        bootstrap_generations: 3
        release_tags: "pinned"
        quarantine_days: 7
        tmp_hours: 24
```

These numbers are starting points, not language semantics. An automatic policy should use both an absolute reserve and a filesystem percentage. Explicit administrator configuration wins.

Definitions:

```text
high watermark
    Start normal GC.

low watermark
    Stop GC after enough headroom has been restored.

hard limit
    Reject or skip new cache writes when eviction cannot keep pace.

minimum free reserve
    Trigger emergency GC even if cache-accounted bytes are below max.
```

A normal build does not fail because a cache write was rejected.

## 18.3 Roots and leases

GC roots:

```text
active action/result leases
in-flight uploads and atomic publications
explicit user/admin pins
current workspace last-successful manifests
retained main action generations
current and retained bootstrap catalogs
release-tag manifests
verification evidence explicitly retained by policy
toolchain/schema artifacts required by retained actions
```

A lease is created before materializing or mapping an artifact and released after the consumer is finished. Leases contain process identity, creation time, heartbeat/generation, and referenced manifest/artifact digests.

Stale leases may be reclaimed only after proving their owning process/session is dead or after a conservative timeout plus generation check.

## 18.4 Two-level GC

### Fast GC

Runs frequently:

1. Delete expired temp files.
2. Delete expired quarantine files according to policy.
3. Expire remote-branch action mappings past TTL.
4. Evict unpinned action mappings in lowest-value namespaces.
5. Use approximate reference counts to identify CAS blobs with no remaining action/manifest references.
6. Atomically rename candidates into `trash/`.
7. Delete trash asynchronously.

### Full mark-and-sweep

Runs periodically or after metadata inconsistency:

1. Snapshot pins, retained action mappings, and active leases.
2. Mark result manifests reachable from those roots.
3. Recursively mark dependency manifests, AOP group manifests, block manifests, packs, chunks, and artifact blobs.
4. Compare marked closure with the physical CAS.
5. Move unmarked objects to `trash/` atomically.
6. Revalidate the retained action-manifest closure.
7. Rebuild or repair approximate reference counts and size metadata.
8. Delete trash after a grace period.

Reference counts are an optimization, not the source of truth. Mark-and-sweep repairs drift after crashes or races.

## 18.5 Eviction ranking

Safety is determined first. Among deletable action roots, rank by:

```text
namespace protection class
expiration/TTL status
last access time
access frequency
recomputation cost
unique retained bytes
artifact size
toolchain/target relevance
```

Suggested protection order, lowest value first:

```text
expired temporary/quarantine
orphaned schema generations
expired branch namespace
unreferenced dirty-worktree actions
old feature-branch actions
old machine-local actions
old unpinned main actions
retained main generations
bootstrap roots
release pins
active leases
```

A cost-aware policy can retain a rarely used but very expensive compiler stage over a frequently used tiny parse result. Keep the policy deterministic and observable.

## 18.6 Admission under storage pressure

Before a large write:

1. Estimate or reserve the maximum expected bytes where possible.
2. Check cache-accounted size and filesystem free reserve.
3. Run fast GC when above high watermark.
4. Reject the cache write when above hard limit or below minimum reserve.
5. Continue the build without caching.
6. Emit one rate-limited diagnostic and status metric.
7. In remote service mode, return a clear resource-exhausted response; do not accept half an action closure.

If protected roots alone exceed the configured maximum, report:

```text
PinnedOverflow:
    protected_bytes
    configured_max
    largest_roots
    suggested unpins or limit increase
```

Never delete protected roots merely to claim that the maximum was met.

## 18.7 Crash safety

- Write immutable content to a private temp path.
- Hash while writing and verify before publication.
- Flush data and required metadata according to platform policy.
- Publish by atomic rename.
- Publish action mapping only after all referenced blobs exist.
- GC first renames to `trash/`; lookup ignores trash.
- A lost CAS write race is success only when the existing bytes verify to the requested digest.
- Startup cleans abandoned temp files, resumes/deletes trash, verifies schema, and samples or fully checks metadata consistency.
- Corrupt entries move to quarantine and become misses.

Access timestamps are journaled or batched; do not synchronously rewrite metadata on every hot hit.

---

# 19. Generated Lean 4 verification plan

## 19.1 Extend, do not replace, the existing cache-identity proofs

The repository already has:

```text
src/verification/cache_identity/
    Model.lean
    Theorems.lean
```

It proves canonical field coverage, `no_false_hit`, AOP-field visibility, order independence, and stamp-fast/strict equivalence. Extend this into a broader cache protocol model.

Suggested layout:

```text
src/verification/cache_protocol/
    Generated/
        Schema.lean
        ActionKey.lean
        AopRules.lean
        BlockRules.lean
        GcRules.lean

    CacheIdentity.lean
    TierModel.lean
    PromotionModel.lean
    AopCacheModel.lean
    BlockDependencyModel.lean
    GcModel.lean
    ConcurrentStoreModel.lean
    TraceChecker.lean

    Theorems/
        IdentitySoundness.lean
        PromotionSafety.lean
        AopInvalidationSoundness.lean
        BlockReuseSoundness.lean
        GcSafety.lean
        PublicationAtomicity.lean
```

## 19.2 One declarative source of truth

Create a schema such as:

```text
src/compiler/80.driver/cache/schema/cache_protocol.sdn
```

It declares:

- action-key fields and canonical order,
- set/map normalization rules,
- domain tags and versions,
- tier and trust states,
- result-manifest closure,
- AOP invalidation dimensions,
- block reuse preconditions,
- GC roots and transitions,
- promotion preconditions,
- diagnostics and state names.

The generator emits:

1. Simple structs/enums and canonical encoder code.
2. Lean structures and canonical model definitions.
3. Field-completeness theorem instances.
4. AOP invalidation rule tables and coverage lemmas.
5. Block reuse transition constructors.
6. GC transition constructors.
7. Cross-language serialization golden vectors.
8. An exported-name contract for durable manual proofs.
9. A schema digest included in every cache identity.

The generated and handwritten layers stay separate. Regeneration may replace `Generated/*`; it must not overwrite `Theorems/*`.

## 19.3 Proof model

```lean
structure CacheState where
  cas              : Digest → Option Blob
  manifests        : Digest → Option Manifest
  actionIndexes    : Namespace → ActionKey → Option Digest
  receipts         : Digest → Option PromotionReceipt
  pins             : Finset Digest
  leases           : Finset Digest
  trash            : Finset Digest
  quarantine       : Finset Digest
  namespacePolicy  : Namespace → Policy
```

Transitions:

```text
PutBlob
PutManifest
PublishLocalAction
PublishBranchAction
PromoteMainAction
LookupAction
AcquireLease
ReleaseLease
Pin
Unpin
ExpireBranch
GcSelectRoots
GcMark
GcMoveToTrash
GcDeleteTrash
Quarantine
InvalidateAopGroup
ReuseBlockResult
RecomputeBlockResult
```

Core predicates:

```text
WellFormedCas
ManifestClosure
WellFormedActionIndex
TrustedMainEntry
AopSelectionConsistent
AopWeaveConsistent
BlockReusePreconditions
GcReachabilitySafe
LeaseSafe
DeterministicAction
```

## 19.4 Required theorem set

### Identity and tier soundness

```text
canonical_encode_injective
all_semantic_fields_visible
local_hit_sound
machine_hit_sound
remote_main_hit_sound
strict_fast_equivalent
same_action_has_unique_result_or_detected_conflict
```

These are conditional on explicit assumptions such as cryptographic collision resistance and deterministic action execution.

### Promotion safety

```text
only_trusted_transition_writes_main
promotion_requires_clean_tree
promotion_requires_authenticated_main_snapshot
promotion_requires_commit_reachability
feature_branch_without_receipt_cannot_write_main
squash_commit_without_ancestry_cannot_promote
promotion_preserves_action_and_result_digest
```

Lean proves the state-machine policy. Git cryptography, CI identity, and remote authentication are trusted boundary inputs represented by checked receipts.

### AOP invalidation

```text
advice_body_symbolic_preserves_selection_key
advice_body_symbolic_preserves_weave_key
embedded_advice_body_change_changes_weave_key
advice_interface_change_is_visible
pointcut_query_change_is_visible
pointcut_scope_change_is_visible
new_candidate_changes_partition_root
selector_readset_disjoint_change_preserves_selection
conservative_unpublicized_mode_has_no_false_hit
selection_delta_reweaves_all_and_only_changed_targets
```

"All and only" may be split into soundness and precision theorems; safety is mandatory, precision may be improved incrementally.

### Block reuse

For deterministic local passes:

```text
same_block_key_and_inputs_same_result
unchanged_transfer_and_input_preserves_output
green_output_stops_successor_invalidation
incremental_dataflow_equals_full_fixed_point
ambiguous_block_match_falls_back_to_function
postweave_block_identity_depends_on_weave_plan
function_summary_equal_stops_external_propagation
```

The generic dataflow theorem assumes a finite lattice and monotone transfer functions. Individual analyses instantiate and prove those obligations.

### GC and publication

```text
mark_contains_all_roots
mark_closed_under_manifest_references
sweep_preserves_marked_objects
gc_preserves_active_leases
gc_preserves_pins
retained_action_closure_valid_after_gc
pinned_overflow_reports_instead_of_deleting
cas_put_idempotent
atomic_publish_never_exposes_partial_closure
trash_objects_are_not_served
quarantine_objects_are_not_served
```

### Concurrency and nondeterminism

```text
same_digest_concurrent_put_converges
action_mapping_conflict_is_detected
gc_and_reader_safe_under_lease
publication_order_preserves_manifest_closure
```

## 19.5 Generated theorem coverage

For every schema field or invalidation dimension, generate a theorem instance and a coverage manifest.

Example:

```lean
theorem pointcutQuery_change_visible ...
theorem ownerScope_change_visible ...
theorem matcherSchema_change_visible ...
theorem candidateRoot_change_visible ...
theorem adviceInterfaceRoot_change_visible ...
```

CI compares:

```text
number and names of semantic schema fields
==
number and names of generated field-coverage theorems
```

Adding an action-key field without a theorem is a generation failure.

## 19.6 Implementation correspondence

Formal proofs over an abstract model are insufficient unless implementation behavior is tied to that model.

Required correspondence gates:

1. **Shared generation:** Simple and Lean identity types/encoders come from the same SDN schema.
2. **Golden vectors:** Simple-generated canonical bytes exactly match Lean-generated/reference bytes.
3. **Regeneration gate:** Generated files must be current and the Git diff clean after regeneration.
4. **No trust bypass:** Scan cache proof roots for `sorry`, `admit`, unexpected `axiom`, and unapproved unsafe/trusted declarations.
5. **Executable trace checker:** The compiler emits canonical cache transition traces; a Lean-built checker replays representative and adversarial traces.
6. **Differential tests:** Cached and from-scratch builds produce identical semantic and artifact digests.
7. **Strict shadow mode:** Fast local, machine, and remote hits are compared against strict full-hash and/or recomputation during rollout.
8. **Schema pin:** The schema digest and Lean toolchain identity enter cache/proof result keys.

Routine structural lemmas may be generated from templates. Core semantic proofs remain durable manual Lean code that imports generated definitions.

## 19.7 Mission-critical formal gate

A mission-critical cache release requires:

```text
lake build
simple gen-cache-model compare
simple cache verify --strict
simple verify check
no sorry/admit/unapproved axiom scan
cross-language golden vectors
AOP invalidation mutation suite
block incremental versus full fixed-point suite
GC failure-injection suite
remote promotion adversarial suite
clean versus cached release artifact digest equality
```

A cache hit is an optimization, not proof evidence by itself. Verification state and signed provenance must remain independently inspectable.

---

# 20. CLI, diagnostics, and configuration

## 20.1 Commands

```text
simple cache status
simple cache stats
simple cache namespaces
simple cache explain <query-or-entity>
simple cache why-miss <query-or-entity>
simple cache verify --strict
simple cache doctor
simple cache gc --dry-run
simple cache gc --to-size <bytes>
simple cache pin <manifest-or-build>
simple cache unpin <pin>
simple cache promote --receipt <receipt>
simple cache trace --output <path>

simple aop cache explain <pointcut-or-target>
simple aop cache diff <old-generation> <new-generation>

simple build explain <target>
simple build why-rebuilt <entity>
simple build --cache=off|local|machine|remote-read|remote-read-write
```

`cache promote` must reject execution outside an authenticated trusted-builder context.

## 20.2 Explain output

```text
query/action key
semantic input fields
source and dependency fingerprints
resolution receipt
AOP surface/candidate/selection/weave roots
block manifest and changed block set
tier lookup sequence
hit/miss reason per tier
provenance and trust class
artifact closure verification
GC protection/eviction status
strict comparison result
```

Example:

```text
target: compiler.semantic::infer_call
workspace: miss — incoming block state changed
machine: miss — AopSelectionDigest changed
remote-main: miss — exact ActionDigest absent
recomputed blocks: 17, 19
green after recompute: block 19 output unchanged
propagation stopped before block 23
weave: reused
advice implementation: fetched from remote-main
component pack: rebuilt
```

---

# 21. Parallel-agent implementation plan

This extends the prior A0–A13 plan. Freeze shared schemas first, then permit parallel work with exclusive file ownership.

## Wave C0 — serial contract freeze

### Agent C0 — Cache protocol and formal schema owner

**Owns**

```text
src/compiler/80.driver/cache/schema/
doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md
```

**Delivers**

- cache tier/trust enums,
- namespace model,
- result and promotion manifests,
- AOP group identities,
- block key/input/result schemas,
- GC root/lease/state schemas,
- canonical encoding rules,
- generator input and exported-name contract.

**Gate**

- Canonical order fixed.
- Every semantic field classified as key, provenance, local state, or GC metadata.
- No production agent invents another cache key.

## Wave C1 — parallel foundations

### Agent C1 — Local and machine CAS/tier router

**Owns**

```text
src/compiler/80.driver/cache/cas_store.spl
src/compiler/80.driver/cache/tier_router/
src/compiler/80.driver/cache/action_index/
```

**Delivers**

- wire existing CAS into local/machine paths,
- immutable result manifests,
- exact lookup and read-through/backfill,
- action-mapping conflict detection,
- process single-flight,
- binary-safe streaming and strict digest verification.

### Agent C2 — Remote-main policy and provenance

**Owns**

```text
src/compiler/80.driver/cache/remote/
src/compiler/80.driver/cache/promotion/
scripts/cache/promotion/
```

**Delivers**

- remote client/protocol adapter,
- repository identity,
- authenticated main snapshot receipt,
- Git ancestry gate,
- signed `PromotionReceipt`,
- main/branch namespace policy,
- squash/rebase handling,
- read-only developer mode.

### Agent C3 — Quota, metadata, leases, and GC

**Owns**

```text
src/compiler/80.driver/cache/gc/
src/compiler/80.driver/cache/lease/
src/compiler/80.driver/cache/metadata/
```

**Delivers**

- high/low/hard watermarks,
- disk free-space reserve,
- fast eviction,
- full mark-and-sweep,
- pins and active leases,
- crash-safe trash/quarantine cleanup,
- refcount repair,
- dry-run/explain reports.

C3 does not edit `cas_store.spl`; it consumes the storage API owned by C1.

### Agent C4 — AOP cache groups

**Owns**

```text
src/compiler/85.mdsoc/aop_cache/
src/compiler/85.mdsoc/aop_index/
```

**Delivers**

- AOP group manifests,
- candidate Merkle partitions,
- selector read sets,
- reverse dependency tables,
- per-target selection shards,
- precise invalidation transaction,
- public/private/conservative trust eligibility.

### Agent C5 — Block dependency and result cache

**Owns**

```text
src/compiler/50.mir/incremental/
src/compiler/60.optimizer/incremental/
```

**Delivers**

- stable `BlockKey`,
- block/region manifests,
- incremental dataflow worklist,
- function fallback,
- pass eligibility policy,
- small-result packing,
- pre/post-weave identity derivation.

### Agent C6 — Generated Lean model and theorem library

**Owns**

```text
src/app/gen_cache_model/
src/verification/cache_protocol/
scripts/check/check-cache-protocol-formal.shs
```

**Delivers**

- SDN-to-Simple and SDN-to-Lean generator,
- generated field-coverage theorems,
- promotion/AOP/block/GC models,
- durable manual proof modules,
- no-trust-bypass gate,
- executable trace checker,
- cross-language golden vectors.

### Agent C7 — SSpec and adversarial fixtures

**Owns**

```text
test/01_unit/compiler/cache_v2/
test/02_integration/compiler/cache_v2/
test/03_system/compiler/cache_v2/
scripts/check/check-cache-v2-*.shs
```

No production compiler edits.

**Delivers**

- branch/main history fixtures,
- corruption and poisoning cases,
- concurrent put/GC/read cases,
- AOP mutation matrix,
- block CFG mutation matrix,
- disk-pressure and crash-recovery tests,
- clean/cached equivalence harness,
- baseline performance telemetry.

## Wave C2 — integration

### Agent C8 — Semantic query/build integration

**Depends on:** C1, C3, C4, C5

**Owns**

```text
src/compiler/80.driver/cache_integration/
src/compiler/80.driver/query_store/
```

**Delivers**

- query result manifests,
- workspace query DB to machine/remote artifact bridge,
- AOP and block roots in action keys,
- exact tier lookup,
- strict shadow comparison,
- diagnostics and explain paths.

### Agent C9 — CI promotion and remote service integration

**Depends on:** C1, C2, C3, C6

**Owns**

```text
.github/workflows/cache-*
scripts/ci/cache-*
src/app/cache_gateway/
```

**Delivers**

- trusted-main writer workflow,
- optional branch namespace,
- policy gateway or existing remote-cache backend adapter,
- signed receipts,
- remote quota/TTL enforcement,
- metrics and administration.

### Agent C10 — Bootstrap/component cache integration

**Depends on:** C8

**Owns**

```text
scripts/bootstrap/cache/
src/app/cli/native_build_cache_v2/
```

**Delivers**

- componentized bootstrap lookup,
- retained bootstrap roots,
- selected-backend closure caching,
- strict release/bootstrap policy,
- no full-source probe on warm component build.

## Wave C3 — certification

### Agent C11 — Formal and adversarial certification

**Depends on:** C7, C8, C9, C10

**Owns**

```text
src/verification/cache_protocol/certification/
doc/09_report/cache_v2_certification_*.md
```

**Delivers**

- proof gate results,
- strict/fast/tier parity,
- clean/cached artifact equality,
- remote-main attack simulation,
- GC model/implementation trace equivalence,
- AOP precision and soundness report,
- block incremental/full-analysis equivalence,
- production-readiness decision.

## Merge order

```text
C0
↓
C1 + C2 + C3 + C4 + C5 + C6 + C7
↓
C8 + C9
↓
C10
↓
C11
```

## Coordination rules

1. C0 schemas are frozen before parallel implementation.
2. C1 is the sole owner of `cas_store.spl`.
3. C3 accesses CAS only through the C1 API.
4. C4 and C5 emit manifests; C8 is the sole owner of query/action-key wiring.
5. C6 owns generated formal artifacts and manual cache-protocol proofs.
6. C7 owns tests but not production fixes.
7. C9 is the sole owner of remote-main write credentials/workflows.
8. Each agent supplies an invalidation table and `cache explain` evidence.
9. No agent declares cache correctness from hit-rate tests alone.
10. C11 alone declares the feature release-ready.

---

# 22. Migration sequence

## Phase 0 — observability and schema

- Land C0 schema and generator.
- Record current cache size, build times, file reads, MIR cache usage, and invalidation breadth.
- Add `cache explain` without changing reuse behavior.
- Extend existing Lean identity model in compute-only mode.

## Phase 1 — local/machine CAS with bounded storage

- Wire existing CAS into immutable action/result paths.
- Add metadata, watermarks, leases, and GC before enabling broad writes.
- Keep legacy cache authoritative; shadow-compare.
- Verify strict hash parity and corruption behavior.

## Phase 2 — workspace semantic query integration

- Persist declaration/function query records.
- Store immutable query results in machine CAS.
- Keep query graph workspace-local.
- Retire ad hoc filename-sanitized MIR cache paths after equivalence tests.

## Phase 3 — remote-main read-only

- Deploy remote CAS/action backend.
- Developer and branch builds read main only.
- Verify all blobs and manifests.
- Collect hit/miss and non-hermetic-key diagnostics.
- No remote writes from local machines.

## Phase 4 — trusted main publication

- Enable main CI receipts and protected writer.
- Detect action mapping conflicts.
- Pin current bootstrap/release roots.
- Keep branch cache disabled initially.

## Phase 5 — optional branch namespace and promotion

- Add trusted branch CI namespace with TTL/quota.
- Implement post-merge ancestry promotion.
- Keep rebuild-on-main as default.
- Test merge, rebase, squash, cherry-pick, force-push, and deleted-branch cases.

## Phase 6 — AOP group cache

- Shadow the precise group invalidation against conservative whole-scope invalidation.
- Require identical selected target/advice sets.
- Enable public scoped groups first.
- Keep legacy unpublicized groups conservative.
- Mission-critical mode rejects unpublicized cross-scope use.

## Phase 7 — block-level cache

- Start with dataflow transfer results and diagnostics.
- Enable only for selected large/expensive functions.
- Shadow every reused result against full-function analysis.
- Add region reuse.
- Defer block machine-code emission.

## Phase 8 — bootstrap and release default

- Enable componentized bootstrap reads from trusted main.
- Normal development uses local/machine/remote-read.
- Release performs strict verification, proofs, provenance validation, and clean/cached equality.
- Remove legacy path-keyed cache authority.

---

# 23. Acceptance criteria

## Tiering and promotion

- Dirty worktree writes no remote-main entry.
- Feature branch reads an exact main-cache result.
- Trusted branch namespace cannot modify main.
- A normally merged branch receipt promotes after ancestry verification.
- A squash-merged branch receipt is rejected for direct promotion.
- A stale or unauthenticated `origin/main` snapshot cannot authorize promotion.
- Same action mapped to different result manifests is detected and quarantined.
- Remote unavailable/full falls back to local execution.

## Storage and GC

- Cache remains below hard limit or reports protected overflow.
- GC reaches low watermark when enough deletable data exists.
- Active reader survives concurrent GC.
- Pinned release/bootstrap roots survive.
- Expired branch entries are removed before retained main entries.
- Missing or corrupt metadata is repairable by full mark-and-sweep.
- Crash between blob publication and action publication exposes no partial hit.
- Corrupt blob or manifest becomes a miss and quarantine event.

## AOP

- Advice body-only symbolic change causes no target reweave.
- Advice interface or ordering change reweaves every affected target.
- Pointcut query/scope change reevaluates the correct candidate partitions.
- New matching target changes the relevant partition and selection.
- Unrelated descriptor-field changes do not reevaluate a selector that does not read them.
- New imported aspect invalidates affected visible-aspect catalogs.
- Runtime activation generation is never served from persistent global cache.
- Precise and conservative matchers produce identical behavior.

## Block level

- Stable blocks survive unrelated edits and line movement.
- Ambiguous structural correspondence invalidates the function.
- Incremental dataflow reaches the same fixed point as full analysis.
- Unchanged outgoing state stops propagation.
- Loop/region changes invalidate the necessary SCC.
- AOP selection changes invalidate affected block/region analyses.
- Final function summary and emitted artifacts match a clean build.
- Cache overhead does not exceed recomputation benefit on small functions; policy disables it.

## Formal

- Generated Simple and Lean encoders match all golden vectors.
- Every semantic schema field has a field-visibility theorem.
- `lake build` passes with no `sorry`, `admit`, or unapproved axiom.
- Promotion, AOP, block, GC, and concurrency theorem suites pass.
- Executable Lean checker accepts valid implementation traces and rejects mutated invalid traces.
- Strict no-cache, local-cache, machine-cache, and remote-main builds produce identical output digests.
- A deliberately omitted key field makes the generated coverage gate fail.

---

# 24. Additional non-negotiable invariants

1. Git history controls **admission**, never semantic action identity.
2. A branch name alone never authorizes main-cache publication.
3. CAS digest verification does not replace trusted action-mapping provenance.
4. No approximate or prefix cache key may return a compiler artifact.
5. Workspace query state is not remotely shared until all IDs and read sets are proven stable.
6. Negative resolver/cache entries are local and short-lived.
7. AOP storage packing never couples logical invalidation.
8. Advice implementation is excluded from a weave key only when the target contains a symbolic reference and no body semantics are embedded.
9. Block cache reuse requires equal canonical block semantics, equal relevant dependencies, equal incoming analysis state, and equal pass schema.
10. Uncertain block correspondence falls back to function recompilation.
11. GC may produce a false miss but never a dangling successful hit.
12. Action mappings are published only after complete artifact closure.
13. A protected-root overflow is reported; safety is not sacrificed to a size target.
14. Cache write failure cannot change build output.
15. Mission-critical mode quarantines and recomputes on any inconsistency.
16. Runtime AOP state, JIT addresses, and loader generations remain session-local.
17. Generated verification definitions and durable manual proofs remain separate.
18. Formal claims explicitly state assumptions: cryptographic collision resistance, deterministic compiler actions, atomic filesystem primitives, and trusted CI/remote-snapshot boundaries.

---

# 25. Recommended first integrated milestone

Implement only this vertical slice first:

1. Shared cache-protocol SDN schema and generated Simple/Lean types.
2. Existing CAS wired as local and machine immutable storage.
3. Result manifest closure and exact action index.
4. High/low/hard storage watermarks, leases, and mark/sweep GC.
5. Remote-main **read-only** client.
6. Trusted main receipt model, but keep writes disabled.
7. AOP public-surface, candidate-partition, selection, and advice-implementation digests.
8. One block-level dataflow cache with whole-function fallback.
9. Lean proofs for identity, GC root preservation, symbolic advice body separation, and block transfer reuse.
10. Strict shadow comparison against clean recomputation.

Only after that milestone has zero divergence should remote-main writes, branch promotion, broader AOP group reuse, and more block-level passes be enabled.

---

# References

- [R1] Brian de Alwis and Gregor Kiczales, *Apostle: A Simple Incremental Weaver for a Dynamic Aspect Language*, UBC Technical Report TR-2003-16, 2003.
- [R2] Eclipse AspectJ Development Guide, *Bytecode weaving, incremental compilation, and memory usage*.
- [R3] William G. Griswold et al., *Modular Software Design with Crosscutting Interfaces*, IEEE Software 23(1), 2006, DOI 10.1109/MS.2006.24.
- [R4] Matthew A. Hammer et al., *Incremental Computation with Names*, OOPSLA 2015.
- [R5] Rust Compiler Development Guide, *Incremental compilation* and the red/green algorithm.
- [R6] Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones, *Build Systems à la Carte: Theory and Practice*, Journal of Functional Programming 30, 2020.
- [R7] Bazel documentation, *Remote Caching*.
- [R8] Git documentation, `git merge-base --is-ancestor`.
- [R9] GitHub Actions documentation, branch cache restrictions, cache security, limits, and eviction.
- [R10] Nix documentation, garbage-collector roots and mark/sweep store collection.
- [R11] SLSA Build requirements and threats, cache poisoning and provenance.
