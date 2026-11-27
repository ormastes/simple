# P0: cache, semantic constraints and codec readiness

Baseline: 4fccb94e564b25a0a2effdd711113da5a1b1e20c, isolated foundation worktree. Read-only source inventory; no source changes, runtime commands or qualification claims. PR-A must change no behavior. Experimental H and broad C are excluded.

## Current codec authority

`src/compiler/20.hir/hir_codec.spl:42` declares legacy `spl-hircodec-v14-runtime-value-extern-provenance` and canonical `spl-hircodec-canonical-v5-a5-refusal`. Canonical identity incorporates the header, flat-pool version and canonical rules digest. However `hir_canonical_codec_generated_available_v1` at line69 returns **false** intentionally. Both canonical encode and canonical decode refuse with `canonical_codec_generator_stale`. Thus canonical descriptor/API scaffolding exists on this baseline, but usable canonical HIR bytes do not. Historical descriptions saying canonical support is absent should be refined to this exact state; descriptions claiming usable canonical serialization are incorrect.

Legacy `hir_module_encode` remains available but refuses modules with representation declarations and other unsupported payloads. A nonempty legacy encoding is not proof of canonicality, immutable ownership, complete semantic coverage or compiler qualification. `hir_codec_support.spl` and generated encoding remain the refusal/coverage authorities.

`src/compiler/20.hir/generated/hir_codec.spl` is generator-owned. Its header specifies `bin/simple run src/app/compiler_schema/main.spl codec`. The canonical gate explicitly requires an admitted self-hosted runtime regeneration plus independent real-HIR golden-byte review. P0 and PR-A must neither regenerate nor flip that gate. Future schema changes need generator-source alignment, fresh generated artifacts, roundtrip/refusal tests and admission evidence; do not hand-edit generated code or make the new overlay depend on whole-HIR serialization.

## Existing HIR cache contract

`driver_hir_cache.spl:203–246` already avoids the historical unconditional cross-target alias hazard. Default keys retain `hir-target-v2`, guard-context identity and the explicit native-target text. With cfg-select enabled, only a declared marker-mode parse with zero strip decisions **and** a closure proven entirely neutral substitutes `hir-target-neutral-v1`. Unknown evidence, unmanaged parse or any stripping retains target identity and strip-decision digest. This is conservative target-dependent cache separation, not an observed-target-read implementation or proof that all source alternatives survived.

`hir_cache_key` also binds source/path/closure, entry role, environment switches and codec header. Parser-selected cache paths have a separate suffix and binding admission. Preserve these authorities in PR-A; deleting target components before retained alternatives and complete dependency evidence exist would be unsound.

## Semantic positive/negative read contracts

`common/cache_contract/semantic_query_read_manifest_v1.spl` already defines producer/consumer query keys, semantic profile and parameter digests, consumed fingerprint, witness digest, partition and coverage (Complete/Conservative/Unknown). Read kinds are Positive, Absence and Membership, encoded through facet prefixes. `snapshot_contract_v1` and `canonical_cache_codec_v1` transport negative candidate absence witnesses and directory generations; sorting/duplicate checks protect canonical snapshot identity. These are reusable contracts, not evidence that HIR/MIR target accesses already emit them.

The bounded target-reader search did not identify a concrete observed-target-read recorder wired into MIR guard evaluation. Do not infer implementation from generic manifest types. `ProviderManifestV1.target_constraints:[text]` is provider metadata, not the new persistent target-neutral semantic-constraint graph. The new plan needs inventory-backed mapping of each target query to positive value reads, absent feature/candidate reads and complete membership reads; unknown coverage must remain conservative. PR-A only names/access-wraps existing authority, without changing cache keys or admitting new hits.

## Final-object and streaming boundary

`driver_aot_native_output.spl:2429` admits ordinary object cache candidates only with matching source snapshot and module witness; it requires scoped existing outputs and a current MIR/storage capsule receipt. Public interface identity alone is explicitly insufficient because generic/default bodies and static initializers can affect consumers. Consequently this cache path still consumes current MIR; it is not a pre-MIR streaming warm-hit proof.

`driver_pipeline_lowering.spl:1320` has a distinct opt-in prelower object cache. It skips MIR only when **every** scheduled module hits. `driver_native_prelower_cache.spl` explains why: lowerers share cross-module inventories, so partial skips could change remaining MIR. Stored entries publish last and lookup rehashes objects. The admission function explicitly warns UNQUALIFIED, rejects staged/sharded, demand, cold-receipt, collection-budget, emit-object and bootstrap routes. This is neither an admitted production optimization nor the requested per-unit streaming final-OBJ boundary.

Future target overlays must preserve verified final-object warm hits before unnecessary HIR/TargetHIR/MIR work where the selected route proves that authority. A miss should materialize only its required unit/dependencies; do not insert a whole-program preparation barrier. A final-object hit must bind target, compiler/backend, semantic constraints and complete observed positive/negative reads, plus actual object integrity. Partial reuse needs an ownership/dependency proof replacing today's all-or-nothing inventory assumption. P0 records that gap; PR-A does not repair it.

## Acceptance inventory for later phases

- Canonical availability refusal remains exact until generator admission; legacy compatibility unchanged.
- Equal source under different target-sensitive strip decisions cannot alias; unknown neutrality stays target-bound.
- Positive target changes, newly present formerly absent features/names and membership changes invalidate exactly the dependent consumers; unrelated target facts must not invalidate proven-independent entries.
- Warm final-OBJ admission must demonstrate no unnecessary full-HIR decode/encode, clone, freeze or whole-closure preparation; cold/miss paths retain precise failure diagnostics.
- Failed/partial reads and stale object receipts refuse reuse. Measure unit latency and peak RSS before changing defaults.

These are planned executable acceptance cases, not tests run by this inventory. Cross-review of the freeze, entrypoint inventories and exact governing plan is recorded below.

## Cross-review receipt

Reviewed the saved governing plan and ownership inventory on this baseline. The plan already records canonical generation refusal accurately; its historical main-source provenance remains historical, while this inventory supplies local release evidence. The ownership inventory correctly separates read-only facade vocabulary, persistent topology and semantic transfer contracts from deep freeze and runtime lifetime enforcement. No confirmed P0/P1 documentation inconsistency was found in that bounded review. PR-A must not advertise mutable container/owner aliases as frozen authority. The saved MIR-entrypoint inventory was subsequently reviewed: its raw-entry, ambient-feature, selected-archive mutation and transient lifetime distinctions match the inspected baseline. No execution evidence was added.
