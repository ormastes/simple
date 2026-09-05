# C0 — Cache protocol schema freeze

**Date:** 2026-08-09
**Schema:** `src/compiler/80.driver/cache/schema/cache_protocol.sdn` (the normative artifact; this note is a reader's digest)
**Design:** `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
**Plan:** `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`
**Status:** FROZEN at `schema_version: 2`. C1–C7 may start.

Any rename, reorder, or removal below is a `schema_version` bump, not a patch.

---

## 1. Canonical field order (ActionDigest)

`domain` is the outer field tag, not an inner field. Positions 1–14 are
**byte-identical** to the v1 encoder in `src/compiler/80.driver/cache/action_key.spl`
and the proven model in `src/verification/cache_identity/src/CacheIdentity/Model.lean`.
Positions 15–20 are the v2 extension, **appended** so the v1 prefix stays provable.

| pos | name | tag | type | class |
|----:|---|---|---|---|
| 0 | `domain` | *(outer tag)* | text | KEY |
| 1 | `compiler_exe` | `compilerExe` | digest | KEY |
| 2 | `live_compiler_src` | `liveCompilerSrc` | digest | KEY |
| 3 | `schema_version` | `schemaVersion` | u32 | KEY |
| 4 | `target_triple` | `targetTriple` | text | KEY |
| 5 | `host_arch` | `hostArch` | text | KEY |
| 6 | `cfg_features` | `cfgFeatures` | set\<text\> (sorted) | KEY |
| 7 | `stdlib_variant` | `stdlibVariant` | text | KEY |
| 8 | `runtime_family` | `runtimeFamily` | text | KEY |
| 9 | `source_content` | `sourceContent` | digest | KEY |
| 10 | `resolution_witness` | `resolutionWitness` | digest | KEY |
| 11 | `deps` | `deps` | set\<dep\> (sorted) | KEY |
| 12 | `macro_root` | `macroRoot` | digest | KEY |
| 13 | `aop_selection` | `aopSelection` | digest | KEY |
| 14 | `ct_env_inputs` | `ctEnvInputs` | set\<text\> (sorted) | KEY |
| 15 | `schema_digest` | `schemaDigest` | digest | KEY |
| 16 | `aop_surface_root` | `aopSurfaceRoot` | digest | KEY |
| 17 | `aop_candidate_partition_roots` | `aopCandidatePartitionRoots` | set\<digest\> | KEY |
| 18 | `aop_weave_root` | `aopWeaveRoot` | digest | KEY |
| 19 | `block_manifest_roots` | `blockManifestRoots` | set\<digest\> | KEY |
| 20 | `result_kind` | `resultKind` | enum | KEY |

**Sentinel rule.** Fields 16–19 have no producer in the tree today. They are
**present in the canonical order from day one** and encode the fixed sentinel
digest of the empty canonical seq until their producer lands. Wiring a producer
changes only the *value*, never the field count or the order — so the C6
`fields == theorems` coverage gate is stable across the whole rollout. **No agent
may omit a field to defer it.**

## 2. Classification table

Exactly one class per field. KEY is the complete list above (21 entries incl. `domain`).

| class | fields | rule |
|---|---|---|
| **KEY** | positions 0–20 above | enters `ActionDigest`; needs a field-visibility theorem |
| **PROVENANCE** | `branch_name`, `source_commit`, `source_tree`, `trusted_ref`, `trusted_ref_tip`, `pull_request_number`, `ci_run_id`, `builder_id`, `user_name`, `signature`, `timestamp` | admission/trust evidence only; lives in `PromotionReceipt` / `NamespacePolicy`. **Never in the key.** |
| **LOCAL_STATE** | `workspace_absolute_path`, `workspace_id`, `worktree_dirty`, `watcher_generation`, `runtime_activation_generation`, `jit_address`, `loader_generation`, `negative_resolution_entry`, **`mir::BlockId`** | workspace/session only; never shared, never in any digest |
| **GC_METADATA** | `last_access_time`, `access_count`, `unique_retained_bytes`, `recomputation_cost_ms`, `artifact_size_bytes`, `ttl_deadline`, `refcount_approx` | eviction ranking only; never affects identity or trust |

Each PROVENANCE/LOCAL_STATE/GC_METADATA entry additionally requires a **negative
(field-absent)** theorem in C6. Moving any of them into `canonical_order` must
fail `scripts/check/check-cache-protocol-formal.shs`.

## 3. Existing proven theorems → extended field set

The ten proven theorems in `src/verification/cache_identity/` all survive
unchanged, because v2 only appends:

| existing theorem | maps to |
|---|---|
| `source_change_visible` | pos 9 `sourceContent` — unchanged |
| `deps_change_visible` | pos 11 `deps` — unchanged |
| `macro_change_visible` | pos 12 `macroRoot` — unchanged |
| `resolution_change_visible` | pos 10 `resolutionWitness` — unchanged |
| `compiler_change_visible` | pos 1–2 `compilerExe`/`liveCompilerSrc` — unchanged |
| `aop_change_visible` | pos 13 `aopSelection` — **retained verbatim**; while 16–18 hold sentinels it remains the *sole* carrier of AOP identity, so this theorem is still the complete AOP soundness statement. When 16–18 gain producers, C6 adds `aop_surface_change_visible`, `aop_candidate_change_visible`, `aop_weave_change_visible` **beside** it, not instead of it |
| `no_false_hit` | re-proved over the 21-field key; the v1 proof is the prefix case |
| `stamp_fast_eq_strict` | unchanged (stamp layer is orthogonal to field count) |
| `deps_reorder_hits` | unchanged; the same sort-then-encode rule now also covers the two new set fields (17, 19), which need `aop_roots_reorder_hits` and `block_roots_reorder_hits` |
| `cfg_reorder_hits` | unchanged |

New obligations C6 owns: `schema_digest_change_visible`, `result_kind_change_visible`,
plus a **prefix-compatibility lemma** — an ActionKey whose fields 15–20 are all
sentinels encodes to the v1 canonical form extended by six fixed suffix fields.

## 4. ResultManifest vs the existing `ActionManifest`

`cas_store.spl` today: `ActionManifest{action_digest, artifact_digests, schema_version}`,
API `cas_open / cas_put / cas_get / cas_has / cas_quarantine / action_put / action_get`.

`ResultManifest` is a strict superset:

- **Kept:** `action_digest`, `artifact_digests`. `schema_version` is kept under the
  name **`producer_schema`** (same meaning: the schema of the writer).
- **New:** `result_kind`, `output_fingerprint`, `dependency_manifest`,
  `aop_group_roots`, `block_manifest_root?`, `diagnostics_digest?`.

Both `cas_store.spl` and `action_key.spl` are Phase-1 with **zero callers**, so
C1 may widen the record without breaking anyone. **C1 is the sole owner of both
files; C0 did not edit them.**

## 5. SPEC-FORWARD inventory (nothing behind it today)

Marked in the schema with `backing: SPEC_FORWARD` and a named `prerequisite:`.

### 5a. AOP — the entire group split

There are **no pointcuts in the tree.** `src/compiler/85.mdsoc/weaving/` implements
join points only: `JoinPointKind{Execution, Decision, Condition, Error, SecurityGate}`,
`JoinPoint{kind, block_id: BlockId, instruction_index, context}`, and a
`WeavingConfig` whose "matching" is an **untyped `WeavingRule.predicate_text: text`**.
All join points are global (no partitioning, no publicization — `CapsuleVisibility`
governs capsule exports, not join points). Weaving **mutates MIR in place**
(`src/compiler/50.mir/mir_aop_injection.spl`); there is no per-target weave artifact.

So `AopSurfaceKey`, `AopSelectionKey` (`normalized_query_digest`,
`matcher_schema_digest`, `visible_aspect_catalog_digest`) and `AopWeaveKey`
describe machinery that **does not exist**. They are defined, not wired.
Prerequisites, in order:

1. a normalized pointcut query type replacing `predicate_text: text`;
2. a typed matcher with a schema digest (nothing produces `matcher_schema_digest` today);
3. join-point publicization/visibility;
4. candidate Merkle partitioning;
5. per-target weave artifacts replacing in-place MIR mutation;
6. a visible-aspect catalog;
7. stable join-point identity (see 5b).

**What the schema degrades to today:** the only descriptor fields a selector can
read are `JoinPointContext.{function_name, module_path, signature, attributes, effects}`.
The nine-value `selector_read_set_fields` list is spec-forward; its backed subset
maps `qualified_name→function_name`, `owning_scope→module_path`, and the other
three by name. `JoinPointKind` is encoded **by name, never by ordinal**, so the
five real values are backed and the eight reserved ones can be appended later
without perturbing any digest.

### 5b. BlockId is an integer index — never a cache key

`src/compiler/50.mir/mir_instruction_support.spl`: `struct BlockId: id: i64`
(entry = `BlockId(0)`). This is exactly the anti-pattern the design forbids.
It is classified **LOCAL_STATE** and appears in
`block.block_key.forbidden_identity_sources`. `BlockKey` is a **new, separate**
stable-identity type: `{parent_function: EntityKey, origin_anchor: StableAstId,
role: BlockRole, structural_path: Digest, same_anchor_ordinal: u32}`.
A `BlockId → BlockKey` mapping table is a C5 prerequisite. Because `JoinPoint`
addresses its target by `BlockId`, **join-point identity is unstable today too** —
that is prerequisite 7 above.

### 5c. No dataflow framework

There is no lattice, no worklist, and no transfer-function abstraction anywhere
in `50.mir` or `60.mir_opt` (a single inline "backwards dataflow" comment in
`dce.spl`). Block-level reuse has **no substrate to attach to**; C5 must build
the framework before `BlockInputFingerprint` means anything.
Note the real path is **`src/compiler/60.mir_opt/`**, not `60.optimizer` as the
plan's ownership table states.

## 6. Exported-name contract

Durable manual Lean proofs (`src/verification/cache_protocol/Theorems/*`) and all
C1–C7 Simple code may import **only** these names. Regeneration may replace
`Generated/*`; it must never overwrite `Theorems/*`.

**Types (29):** `ActionKey`, `ActionDep`, `ResolutionProbe`, `CacheTrust`,
`CacheNamespace`, `ResultKind`, `ResultManifest`, `DependencyManifest`,
`PromotionReceipt`, `AopSurfaceKey`, `AopCandidatePartitionKey`, `AopSelectionKey`,
`AopWeaveKey`, `AdviceInterfaceKey`, `AdviceImplementationKey`, `AopGroupManifest`,
`JoinPointKind`, `WeaveMode`, `BlockKey`, `BlockRole`, `BlockInputFingerprint`,
`BlockResult`, `FunctionBlockManifest`, `CacheLease`, `CacheMetadata`, `CacheState`,
`PinnedOverflowReport`, `AssuranceLevel`, `Visibility`.

**Encoders:** `action_key_encode`, `action_key_digest`, `interface_digest_of`,
`resolution_witness_digest`, then `<name>_encode` / `<name>_digest` for
result_manifest, promotion_receipt, cache_namespace, and `<name>_digest` for the
six AOP keys, `aop_group_manifest`, `block_key`, `block_input_fingerprint`,
`block_result`, `function_block_manifest`, plus `schema_digest_of_protocol`.

**Reused, not regenerated** (from `action_key.spl` — the generator must not emit
a second copy): `canon_str`, `canon_nat`, `canon_field`, `canon_seq`, `canon_dep`,
`action_key_text_lt`, `action_key_text_le`, `action_dep_le`,
`action_key_sort_texts`, `action_key_sort_deps`.

**Lean:** `CacheState`, `Namespace`, `Policy`, `Transition`, `canonicalOrder`,
`fieldClass`, `encode`, `canonKey`. Transition constructors are `gc.transitions`
camelCased (`put_blob → PutBlob`, 19 of them); predicates are `gc.predicates`
camelCased (`well_formed_cas → WellFormedCas`, 10 of them).

**Coverage gate:** `count(canonical_order) + 1 == count(field-visibility theorems)`,
and every `excluded_from_key` entry needs a field-absent theorem.
Enforced by `scripts/check/check-cache-protocol-formal.shs` (C6 owns it).

## 7. Ambiguities in the design doc, and how C0 decided

1. **§16.2 conditional weave-key field.** The doc says the advice-implementation
   digest "must enter `AopWeaveKey`" for embedding modes and must not for
   symbolic calls — a variable field count, which breaks a fixed canonical order
   and the coverage gate. **Decision:** one always-present optional field
   `embedded_advice_impl: digest?`, encoded `Q0:` when absent. Same semantics,
   constant field count.
2. **`result_kind` was not in the design's key list.** Without it an artifact of
   one kind could satisfy a query of another whose other inputs coincide.
   **Decision:** added as KEY, pos 20.
3. **Schema digest placement.** §19.2 says "a schema digest included in every
   cache identity" but never names a field. **Decision:** explicit KEY field
   `schema_digest` (pos 15), alongside the existing numeric `schema_version`.
4. **`aop_group_roots` in `ResultManifest` vs the split roots in the key.**
   The doc uses both. **Decision:** the manifest keeps the flat
   `aop_group_roots: set<digest>` (it is a closure listing for GC marking); the
   *key* uses the split fields 16–18. They are different jobs.
5. **`artifact_digests` ordering.** Unspecified. **Decision:** ORDERED list
   (position is meaningful to the consumer), unlike `aop_group_roots` which is a
   sorted set. Stated explicitly in the schema.
6. **`workspace_id` appears in the namespace path layout** (`actions/workspace/<workspace-id>/`)
   but is LOCAL_STATE. **Decision:** it is a directory selector only and is
   **not encoded** into `cache_namespace`'s digest.
7. **Whether `aop_selection` (pos 13) should be replaced by the split roots.**
   Replacing it would break the v1 prefix and invalidate `aop_change_visible`.
   **Decision:** retain pos 13 verbatim and *refine* it by appending 16–18.
8. **Design's `JoinPointKind` list vs the tree's.** They are disjoint in naming.
   **Decision:** encode by name, record both sets (`values_today` /
   `values_reserved`), and never encode by ordinal.
9. **Optional/bool encoding** is unspecified in v1. **Decision:** optional =
   `seq` of zero-or-one; bool = `nat` 0/1 (the latter already matches
   `resolution_witness_digest`'s `found` handling).
