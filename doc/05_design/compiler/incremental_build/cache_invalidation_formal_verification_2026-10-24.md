# Cache invalidation and update policy — formal verification review and plan

**Status:** review + plan (2026-10-24, `release/1.0.0` @ `dd689c4da9c`, after
#4352–#4397). Companion to the authoritative
[`src_based_tldr_build_v1.md`](src_based_tldr_build_v1.md) and to the
portability review `cache_build_review_and_portability_2026-10-24.md` (sibling,
same day). This document answers four questions: what formal work on the cache
already exists and what it actually covers; which inputs can change an object,
lib, binary, TLDR, AST or generic instance and whether the landed keys and read
manifests capture them; where the update/publication policy has gaps or races;
and which theorems, in which layer, would make the cache *formally verified*
rather than *formally described*. Every claim cites `path:line` at
`dd689c4da9c`; status words follow `src_based_tldr_build_v1.md` (**captured** =
in a live key with a live caller; **partial** = in a shadow-only key or only
one of several paths; **missing** = no key, manifest or read edge records it).

---

## 1. Existing formal work — inventory

| # | Artifact | Kind | What is proved / checked | Entry point | Runs in CI? | Covers current (#4352–#4397) code? |
|---|---|---|---|---|---|---|
| F1 | `src/verification/cache_protocol/` (Lean 4) | **generated + manual proofs** | Generated from `src/compiler/80.driver/cache/schema/cache_protocol.sdn` (v2) by `src/app/gen_cache_model/main.spl`: `Generated/Model.lean` (canonical encoder, injectivity core), `Generated/FieldTheorems.lean` — 21 `*_change_visible` (domain + the 20 `canonical_order` fields, schema `:178-214`) and 27 `*_absent` (every `excluded_from_key` entry, schema `:234-260`), `Generated/Golden.lean` (cross-language golden vectors re-derived at `lake build`), `Generated/Visibility.lean` (48). Manual: `Theorems/Identity.lean` — `source/macro/resolution/compiler/aop_change_visible`, `no_false_hit`, `sentinel_prefix_compat`, `deps/cfg/aop_roots/block_roots_reorder_hits`, `result_kind_differs_misses`; `Theorems/Manual.lean` — `all_semantic_fields_visible`, `aop_group_change_visible`, `v1_prefix_compatible`, `convDep_inj`. | `sh scripts/check/check-cache-protocol-formal.shs` (lake build; no `sorry`/`admit`/`native_decide`/unlisted `axiom`; KEY-field count + 1 == `*_change_visible` count; excluded count == `*_absent` count; regeneration byte-identical) | **No.** Zero hits in `.github/workflows/**` and no row in `config/check/must_check_gates.sdn`; referenced only from `.claude/skills/verify.md`, `.claude/skills/cert_grade.md` and docs | **Shadow path only.** `ActionKey` (`cache/action_key.spl:41-56`) has exactly one Simple constructor site, `cache/integration/shadow_mode.spl:113`, which passes `ct_env_inputs: []`. The live object key is a different composition (§2.0). |
| F2 | `src/verification/cache_identity/` (Lean 4) | manual proofs | Option C core (plan 2026-07-24): canonical encoding injective through canonical form; no omitted-input false hit; a hit returns what re-realization produces; C fast-path SHA == A strict-path SHA when the stamp is valid. Imported by F1. | same gate as F1 | No | Same as F1 — models `ActionKey`, not the live key |
| F3 | `src/verification/build_cache/src/BuildCache.lean` (252 lines) | manual proof *candidate* | `source_change_invalidates`, `generic_body_change_invalidates`, `newer_header_cannot_mask_change`, `absent_committed_header_rejected`, `required_cross_action_rejection`, `current_foreign_owner_poison`, **`claim_preserves_singleflight`**, **`mixed_generation_cannot_publish`**, **`stale_fence_cannot_publish`**, `timeout_without_death_cannot_reclaim`, `completed_publication_blocks_rebuild`, `disconnected_owners_duplicate` (counterexample), `retained_parse_not_repeated`, `cold_then_compile_parses_once`, `reset_invalidates_unowned_handle`, `malformed_restore_rejected`, cold/warm work-cost inequalities | `sh scripts/check/check-lean-proofs.shs` (iterates every Lake project under `src/verification/`) | No (same evidence as F1) | **Models a superseded design.** Header: "Current owner predicates mirror service.spl/coordinator.spl at c48d5fb07cc5" — a *lease + fence + owner-death* single-flight. The landed single-flight (#4372, `cache/daemon/cache_single_flight_v1.spl:20,33,65,79`) is a leader/waiter future table with **no lease, no fence, no owner-death protocol** (`src_based_tldr_build_v1.md` §6). The theorems are true of a model nothing runs. |
| F4 | `src/verification/aop_weaver/src/AopWeaver/Model.lean` (502 lines, no `sorry`) | manual proofs | T1 selection sorted, T2 stable, T3 no-match preserves, T4 deny skips target, T5 deny monotone, T6 proceed linear | `check-lean-proofs.shs` | No | Weaver *semantics*, not cache invalidation. Does not mention `aspect_match_shard_v1`, `selector_digest` or any key. |
| F5 | `src/verification/generic_impl_index/LazyBodyIndex.lean` | manual proofs | `lazy_outputs_equal_eager`, `lazy_index_builds_at_most_once`, `no_index_without_generic_impl` | `check-lean-proofs.shs` | No | Impl-index laziness. No coherence/orphan key theorem. |
| F6 | `src/compiler/40.mono/model/generic_subst_model.spl` laws S1 idempotence, S2 composition, S3 closedness, U1 soundness, U2 most-general, I1 no-evidence ⇒ Unresolved, K1 key determinism, K2 key injectivity on closed types | **bounded-exhaustive SSpec, not proof** (`:18` "Nothing here is a machine-checked PROOF") | specs under `test/01_unit/compiler/mono/model/` | `bin/simple test` | yes, as ordinary tests | Yes — `generic_tldr_view_v1.spl:44` uses `mt_key_type` as the `type_key` of P3 (#4389). K2 is exactly the injectivity the P3 `args_id` needs, but only on a bounded universe. |
| F7 | `test/00_formal_verification/compiler/build_cache_bounded_model_spec.spl`, `build_cache_parse_reuse_spec.spl`, `build_cache_service_refinement_spec.spl`, `cache_correctness_spec.spl`, `cache_invalidate_wildcard_symbol_spec.spl` | finite-domain model checks (SSpec) | production-transition bounds and weighted work; retained-parse reuse; action-ownership refinement; "never returns Verified when fingerprint mismatches"; wildcard-symbol invalidation | `bin/simple test test/00_formal_verification/...` | yes, as tests | Service/coordinator era (`lib.compiler_artifact_service.*`), not the per-file src→obj jobs of `src_based_tldr_build_v1.md` §2 |
| F8 | `semantic_incremental_build_cache_aop_formal_2026-08-09.md` §19.4 | **theorem wish-list** | names 7 identity, 7 promotion, 10 AOP, 7 block-reuse, GC theorems | — | — | Only the identity group exists in Lean (F1/F2). `advice_body_*`, `pointcut_*_is_visible`, `selection_delta_reweaves_all_and_only`, `green_output_stops_successor_invalidation`, `incremental_dataflow_equals_full_fixed_point`, `mark_*` are **unwritten**. That doc carries a superseded banner. |
| F9 | `scripts/check/check-riscv-formal-dual-track.shs` + `doc/06_spec/00_formal_verification/generated_vs_constraints_layout.md` | **the repo's generated-vs-manual pattern** | `GENERATED_CONTRACT.md` + `.byl` emitted from the backend, manual constraint layer kept apart, regeneration checked byte-for-byte | the script | advisory | Pattern to reuse (§4.3); F1 already follows it (`Generated/*` regenerated, `Theorems/*` never touched — `gen_cache_model/main.spl:17-19`). |

**Summary.** The repo has a *real* schema-generated Lean model of a cache key,
with a fail-closed gate and a cross-language golden-vector check. Three things
stop it from being "the cache is formally verified": (1) the modeled key
(`ActionKey`) is not the key the compiler uses to admit an object (§2.0);
(2) the single-flight/publication proofs (F3) describe a lease protocol that
was replaced by #4372; (3) neither Lean gate is wired into any CI job or
`must_check_gates.sdn` row, so a regression in the proofs or the generator would
not fail anything.

---

## 2. Invalidation completeness

### 2.0 Which key is live

There are **three** identities on `release/1.0.0`, and only the third is
Lean-modeled:

1. **Live workspace object/MIR cache** — `src/compiler/80.driver/driver_build/incremental.spl`:
   `DependencyEntry` (`:809-819`: `fingerprint.content_hash` sha256, `dependencies`
   paths, `deps_iface` fold with `"" = unknown (fail closed)`, `interface_digest`,
   `module_witness`) scoped by the cache **directory** name
   `native_build_cache_scope_key` (`:557-592`: `lane;backend;cpu;features;opt;compiler;provider;optimizer`)
   whose `compiler_identity` is `exe=…;compiler=…;runtime=…;bundle=…;simple-abi-policy=…`
   (`:497`), plus `CompileOptionsHash` (`cache/compile_options_hash.spl:112`:
   backend, opt, release, debug_info, gc_off, profile, families, native libs,
   lib paths, linker flags, collection policy/budget, target,
   representation context), plus the environment identity
   `NATIVE_BUILD_SEMANTIC_ENVIRONMENT_FIELDS_V1` (`cache/native_build_environment_identity.spl:7-…`,
   consumed by `driver_aot_native_output.spl`, `driver_build/go_to_end.spl`,
   `driver_native_prelower_cache.spl`, `driver_orchestration.spl`).
2. **TLDR / package headers** — `PublicSummaryV1` (`00.common/cache_contract/public_summary_v1.spl:61-77`:
   `source_blob_digest`, `compiler_owner_digest`, `grammar_digest`, and the
   sections `forward_declarations`, `declarations`, `layouts_abi`,
   `traits_impls_coherence`, `extensions_reexports`, `aop_selectors`,
   `macro_signatures`, `body_refs`, `reverse_reference_roots`);
   `PackageTldrHeaderV1` with `package_tldr_early_cutoff_v1`
   (`cache/package_tldr_metadata.spl:350-367`: producer, package/module identity,
   config variant, smf/export/abi/initializer/provider/generated-source/
   reverse-projection/interface-archive digests).
3. **Shadow `ActionKey` v2** — `cache/action_key.spl:41-56`, schema
   `canonical_order` `:178-214`; **only** constructed in
   `cache/integration/shadow_mode.spl:113` (`SIMPLE_CACHE_V2_SHADOW=1`).

The Lean theorems (F1/F2) are about (3). Everything an object's bytes actually
depend on must therefore be checked against (1) and (2).

### 2.1 Input-by-input matrix

| Input that can change an object / lib / binary / TLDR / AST / instance | Status | Where it is (or is not) captured |
|---|---|---|
| Source bytes | **captured** | `incremental.spl:749` `content_hash` sha256; `:1238-1240` an unavailable hash "cannot certify an unchanged source" (mtime stored `:750` but never decisional); `ActionKey.source_content` |
| Imports / re-exports / visibility | **partial** | `DependencyEntry.dependencies` (paths) + `deps_iface` + `interface_digest` (`:813-816`); `PublicSummaryV1.extensions_reexports` (`:71`). Re-export *chains* (A re-exports B re-exports C; C's interface changes) reach A only if `deps_iface` folds transitively — the fold is one hop per the `DependencyEntry.needs_recompile` history (`.claude/rules/commands.md`). Needs an explicit transitive-closure theorem or a flattened dependency manifest. |
| Name-resolution **absence** (a new file starts shadowing a name) | **partial** | Ordered `probes: [ResolutionProbe{path, found}]` in `native_module_witness.spl:12`, digested by `resolution_witness_digest` (`:121`) into `DependencyEntry.module_witness` (`:819`) and `ActionKey.resolution_witness`. Captured for module paths the resolver *probed*; **not** captured for names that would have been found by a *new* probe the old resolver never issued (e.g. a new `__init__.spl` in a directory that was previously not a package). Schema deliberately excludes `negative_resolution_entry` as LOCAL_STATE (`:253`). |
| Trait impls, coherence, orphan/blanket impls | **missing (cross-module)** | `PublicSummaryV1.traits_impls_coherence` (`:70`) covers impls declared *in the dependency's own interface*. An impl added in module C for a type/trait pair that module A uses, where A does not import C, changes A's method resolution with no edge in A's manifest. No global impl-index digest exists in any key; F5 proves laziness of the index, not its identity. |
| Generic instantiation args | **captured (P3)** | `generic_tldr_view_v1.spl:73-79` `semantic_key`, `template_id`, `args_id`, `snapshot_pin`; `type_key` via `mt_key_type` (K1/K2 bounded, F6) |
| Inline / const fn bodies crossing a module boundary | **missing** | Schema `field_docs.deps`: "INTERFACE digest, not full content digest" (`:222`). `PublicSummaryV1.body_refs` (`:74`) records references, not body bytes. If the backend inlines or const-folds a dependency's body into the consumer's object, the consumer's key does not see a body-only edit. Either inline-eligible bodies must be promoted into the interface digest or the key must carry a `body_digest` read edge. |
| CTFE / compile-time eval inputs (env, clock, files) | **missing** | `35.semantics/const_eval.spl:16,571` reads `env_get(env_name)` at compile time; `ct_env_inputs` exists only in the shadow key and is hardcoded `[]` (`shadow_mode.spl:113`). No clock or file CTFE source was found (`include_str`/`embed` do not exist in the frontend), so env is the only live hole today. |
| `@when` / feature / platform guards (GuardId) | **partial** | `cfg_features` (shadow key only); `config_variant_digest_v1` in the package header (`package_tldr_metadata.spl:359`); macro `guard_ids: [text]` (`macro_reference_manifest_v1.spl:33`); generic `active_guard_root` (`generic_tldr_view_v1.spl:51`). **No `GuardId` type and no static-guard module exist** (`generic_aop_macro_semantic_cache_plan_2026-10-24.md:532`; `ls src/compiler/00.common` has no `static_*`). |
| Macros (definition body, hygiene, effects, dependent macros, missing macro) | **captured (P5)** | `MacroDefinitionEntryV1` `contract_digest`, `body_digest`, `hygiene_schema`, `declared_effects`, `dependent_macros`, `exported_surface_digest` (`macro_reference_manifest_v1.spl:25-37`); unresolved references recorded (`:45-54`); `ActionKey.macro_root` |
| Aspects: pointcut query/scope, advice body, directory membership | **partial (P4)** | `aspect_match_shard_v1.spl`: `selector_digest`, `dir_facts_key`, `complete`, `negative_root`, `sorted_matching_ids`, advice `signature_digest`/`effects_digest` (`:28-63`); `ActionKey.aop_selection`. `aop_surface_root`, `aop_candidate_partition_roots`, `aop_weave_root` are `SPEC_FORWARD` (schema `:203-206`); **advice body → weave key** (`embedded_advice_body_change_changes_weave_key`, F8) has no code. |
| Default parameter values, operator overloads, sealed-enum exhaustiveness | **partial** | Declarations (incl. variant sets and default expressions) are in `declarations`; operator resolution inherits the trait-coherence gap above; exhaustiveness of a downstream `match` changes when the enum's variant set changes — that is an interface change, so captured *if* `deps_iface` reaches it (same transitive caveat). |
| Type layout / ABI | **captured** | `PublicSummaryV1.layouts_abi` (`:69`); `PackageTldrHeaderV1.abi_digest` (`:362`); `simple-abi-policy` in producer identity (`incremental.spl:497`) |
| Compiler binary | **captured** | `exe=` (`native_build_compiler_executable_hash`, `incremental.spl:307`); `ActionKey.compiler_exe` |
| Compiler *source* (self-host lane) | **captured for `src/compiler` only** | `native_build_compiler_source_fingerprint` walks **`src/compiler`** (`incremental.spl:133-150`). |
| Standard library (`src/lib`) version | **missing as producer input** | `src/lib/**` is read as *source* at every run (`.claude/rules/commands.md`) and shapes the compiler's own behaviour, yet it is in neither `compiler=` nor `runtime=`; `ActionKey.stdlib_variant` is a *name*, not a digest. Covered only when a std module appears as an ordinary `DependencyEntry.dependencies` path of user code. |
| Runtime library | **captured** | `runtime=` (`native_build_runtime_provider_fingerprint`, `:334`); `bundle=`; `runtime_std_authority_receipt.spl:59` |
| Codegen backend / target / CPU features / opt-level | **captured** | scope key `:583`; `CompileOptionsHash` `:112` |
| Linker **binary/version** | **missing in key** | `linker_sha256` only in the reproduce receipt (`70.backend/linker/_LinkerWrapper/native_link_reproduce_v1.spl:32-39`); `native_relocatable_linker_version_admissible` (`80.driver/native_relocatable_link.spl:65`) is an *admission gate*, not a key field. A linker upgrade that changes relocation or section layout re-uses a stale link output. |
| Linker flags | **captured** | `compile_options_hash.spl:142-154` `native-linker-flags`; env `LD`, `LDFLAGS` (`native_build_environment_identity.spl:19-20`) |
| **Link order** / native library list | **partial — order lost** | `_coh_sorted_text` sorts `native_libraries` / `native_library_paths` / flags before hashing (`:84,142-154`). For static archives and `--start-group`-less links, order is semantic (symbol resolution), so two different link orders collide to one key. Schema `ordered_sequences` rule (`:73-78`) exists for exactly this class but the live hash ignores it. |
| System libraries (libc, libm, SDK content) | **missing** | Only *paths/names* enter (`SDKROOT`, `LIBRARY_PATH`, `MACOSX_DEPLOYMENT_TARGET`, `:21-31`), never their content or version. |
| Dynlib export sets / import libraries | **partial** | Simple-produced exports: `PackageTldrHeaderV1.export_digest` (`:361`); externally supplied `.lib`/`.so` import sets: not keyed. |
| Build config / env vars / host config | **captured (over-wide)** | `NATIVE_BUILD_SEMANTIC_ENVIRONMENT_FIELDS_V1` includes `PATH`, `PWD`, `LANG`, `HOMEBREW_PREFIX` (`:11-31`). Sound, but `PWD` contradicts the schema rule that absolute workspace paths are LOCAL_STATE and never hashed (`:79-81`) — it defeats cross-workspace sharing by construction. Host-config retention keys (`~/.config/simple/host.sdn`, #4381) only steer eviction, correctly outside the key. |
| Generated sources | **captured** | `generated_source_identity_digest_v1` (`cache/generated_source_receipt.spl:95`); `PackageTldrHeaderV1.generated_source_digest` (`:365`) |
| Debug info / source paths embedded in objects | **partial** | `debug_info` flag in `CompileOptionsHash`; no `-fdebug-prefix-map`/path-remap anywhere in `70.backend`/`80.driver` (grep empty). With debug info on, objects embed absolute paths, so a cross-workspace hit yields an object whose *debug* semantics differ. Either remap paths before hashing or key on the workspace root when `debug_info` is set. |
| Packed-AST / TLDR codec schema version | **captured** | `FLAT_POOL_CODEC_VERSION`, `FRONTEND_CACHE_ENTRY_VERSION`, magic `"SPLAST\0\1"` (`packed_binary_ast_v1.md:36,145`); `FRONTEND_PARSE_IDENTITY_VERSION_V2` (`frontend_parse_identity_v2.spl:5`); `ReverseReferenceKeyV1.schema_version` (`reverse_reference_key.spl:13`); `ActionKey.schema_version` + `schema_digest` |
| Hash algorithm | **partial** | Schema pins `digest: sha256` (`:50`); the verified-CAS kind registry pins the digest rule per kind inside the registry row (`cas/verified_cas_kind_registry_v1.spl:75-93`); in-memory ids use xxh3-128 (#4373). Digest *text* carries no algorithm tag — a 32-hex xxh3 and a 64-hex sha256 are told apart by length alone, and nothing states "unknown algorithm ⇒ miss". |

### 2.2 Missing-source summary (what a formal completeness theorem would fail on today)

| Missing / partial source | Affects | Smallest fix that makes it key-visible |
|---|---|---|
| Cross-module trait impl / coherence / orphan impl | objects, instances | per-(trait,type) impl-set digest in the TLDR table; consumers record a read edge `(ImplSet, trait_id, type_id) → digest` in `SemanticQueryReadManifestV1` (`:19-32`, kind `Membership`/`Absence` already exist `:217-219`) |
| Inline / const bodies across modules | objects | `body_digest` per inline-eligible fn in `PublicSummaryV1.declarations`, or a `BodyRead` read kind |
| CTFE env reads | objects, TLDR | populate `ct_env_inputs` from `const_eval.spl:571` (`(name, value-or-absent)` pairs) and carry it in the live key, not only the shadow key |
| GuardId / `@when` | TLDR, AST, instances | land `StaticGuardIdV1` + guard table; put the active-guard root in the parse identity and the TLDR header |
| Linker binary/version | binaries, dynlibs | fold `linker_sha256` (already computed, `native_link_reproduce_v1.spl:32`) into the link action key |
| Link order | binaries, dynlibs | encode `native_libraries` as `ordered_sequence`, not sorted set |
| System library content | binaries | digest of resolved `-l` targets at link time as a read manifest on the link action |
| External import libs / dynlib export sets | binaries | same read manifest |
| `src/lib` as compiler-behaviour input | everything in the self-host lane | add `stdlib=<fingerprint of src/lib/**>` to the producer identity (`incremental.spl:497`) |
| Debug-info absolute paths | objects (debug semantics) | path remap, or workspace root in key when `debug_info` |
| Advice body → weave output | woven objects | `aop_weave_root` backing (schema `SPEC_FORWARD`, `:205`) |
| Hash-algorithm tag | all | prefix digests `sha256:`/`xxh3:` and make decode of an unknown prefix a miss |

---

## 3. Update / publication policy — gaps and races

| Concern | Landed state | Gap or race |
|---|---|---|
| Publication = temp file + atomic rename | 4 sites implemented (`src_based_tldr_build_v1.md` §5): `.tldr` (`module_artifacts_v1.spl:150-163`), MIR/manifest (`incremental.spl:600`, #4364), private parse cache, shared parse CAS (immutable no-replace) | `.tldr` temp name still uses the global counter `_module_artifact_tmp_seq_v1` (`:52`), not `{pid}.{xxh3(content)}`; two producers with *different* bytes for one key on the **workspace** path (`incremental_file_write_text`) are last-rename-wins — there is no quarantine on that path. |
| Single-flight | #4372 `cache_single_flight_v1.spl` leader/waiter table, wired into `cache_daemon_main.spl`; **uncalled from the compile path** (`CacheReader` has no caller) | The API exposes `leader_of`/`inflight_count` (`:65,79`) but no abandonment/re-drive path, so the §6 contract "an abandoned future is re-driven by the next requester" has no code — a crashed leader leaves waiters pending. F3's proofs (`claim_preserves_singleflight`, `stale_fence_cannot_publish`) are about the *old* lease design and do not transfer. |
| Generations and `.rr` reverse projection | `ReverseReferenceKeyV1{registry_kind, owner_generation, root_generation, subject_identity, projection_kind, projection_digest, schema_version}` (`reverse_reference_key.spl:6-13`); owner snapshot with `sealed`, `incomplete_families` (`reverse_reference_facts.spl:27-34`); P2 `.rr` projection + preview (#4383) | No round-trip or inverse check exists (grep for `inverse|round.?trip|forward.*reverse` over the `.rr` modules is empty). "`.rr` = inverse of the forward manifests" is a design statement, not a checked property. A `.rr` that omits a consumer silently under-invalidates. |
| Staleness is content, never mtime | `FileFingerprint.modified_time` stored (`:750`) but never decides; empty hash fails closed (`:1240`) | none |
| Quarantine on nondeterminism | shared-CAS writer: same `action_digest` with a different mapping ⇒ `CacheNondeterminism` (`cache_writer_v1.spl:111,156,468`); journal tail quarantine (`:104`); durable publisher ⇒ `NondeterministicAction` (`three_payload_generation_publisher_v1.spl:498-502`); schema response `do_not_overwrite, quarantine_both_mappings, emit_nondeterminism_diagnostic` (`:794`) | Only on the daemon/shared-CAS path. The live workspace cache has no mapping journal, so nondeterminism there is invisible (overwrite). |
| Eviction (#4378) | `CacheRetentionLimitsV1` (memory 1 GiB, storage 10 GiB, branches 4, versions/source 3); `cache_eviction_plan_v1` newest-first per source, branch last-used; over-limit ⇒ **reject write** (`cache_eviction_plan_v1.spl:159`); **uncalled** | Race: a manifest read followed by an object open with eviction in between. Safe only if every reader opens by digest and fails closed on absence (true for `verified_cas_store`; the workspace path opens by *path*). Semantic-neutrality of eviction also needs "no retained manifest references an evicted object" — GC roots/leases are in the schema (`:629-641`) and `gc/mark_sweep.spl`, but the eviction plan does not consult roots. |

---

## 4. Formal verification plan

### 4.1 What to model (Lean 4, extending F1/F2; reuse F3/F4/F6 where they fit)

Notation: `K : Inputs → Key` (live composition of §2.0 item 1 and 2),
`Build : Inputs → Output` (deterministic), `Reads : Inputs → set ReadEdge`
(read manifests), `Inv : Change → set Key` (invalidation).

| # | Theorem (statement) | Layer | Reuses |
|---|---|---|---|
| T-K1 **Key soundness** | `∀ i j, K i = K j → Build i = Build j` (equal key ⇒ equal output), under the stated assumptions: collision resistance of the digest and determinism of `Build`. Proved by `all_semantic_fields_visible` + an **inputs-complete** axiom-free enumeration: every free variable of `Build` is a field of `K` or a recorded read edge. | generated (field list from schema) + manual (`Build` free variables) | F1 `all_semantic_fields_visible`, F2 injectivity |
| T-I1 **Invalidation completeness** | `∀ i, ∀ δ : Change, Build i ≠ Build (δ i) → K i ≠ K (δ i) ∨ ∃ e ∈ Reads i, hits δ e`. Every row of §2.1 becomes a `*_change_visible` or `*_read_edge` instance; the §2.2 rows are the instances that currently cannot be proved — their absence is the honest state and the gate must *count* them, not hide them. | generated (one theorem per schema field and per read kind) | F1 generator: extend `canonical_order` to the **live** key and add a `read_kinds:` block |
| T-I2 **Read-manifest sufficiency** | for the TLDR path: `completeness = Complete → (∀ e ∉ ordered_reads, change e ⇏ Build change)`; `Conservative`/`Unknown` ⇒ the consumer is treated as red | manual over `SemanticQueryReadManifestV1` (`:14-16,35-37`) | — |
| T-RG1 **Red/green early cutoff soundness** | `package_tldr_early_cutoff_v1 prev rebuilt = true → Consumers(prev) need no rebuild`, i.e. the 12 compared digests (`package_tldr_metadata.spl:354-367`) are exactly the fields any consumer may read. Companion: `incremental_dataflow_equals_full_fixed_point` (F8) for the block layer once it exists. | manual; the digest list is generated from the header struct | F8 names |
| T-RR1 **`.rr` is the inverse of the forward manifests** | `∀ subject consumer, (consumer reads subject) ∈ forward ↔ (subject → consumer) ∈ rr`, and `sealed ∧ incomplete_families = []` ⇒ the ↔ is total | manual over `ReverseReferenceOwnerSnapshotV1`; a **bounded-exhaustive SSpec twin** under `test/00_formal_verification/compiler/` (same shape as F7) | F7 pattern |
| T-SF1 **Single-flight linearizability** | for the #4372 leader/waiter table: at most one leader per key (`claim_preserves_singleflight` restated for the future table), every waiter observes the leader's result or a re-drive, and no key has a pending waiter with no live leader (this is the property the current code lacks — the proof will fail until re-drive is implemented, which is the point). | manual; **replace** F3's lease model, keep its statements | F3 statements, new model |
| T-GEN1 **Generation safety** | `publish(owner, gen) succeeds → gen = current` (F3 `mixed_generation_cannot_publish` restated over `ReverseReferenceKeyV1.owner_generation/root_generation`) | manual | F3 |
| T-EV1 **Eviction never changes semantics** | `∀ s, Read (evict s) k ∈ {Read s k, Miss}` and `Miss ⇒ rebuild`, plus `∀ m ∈ retained manifests, refs m ⊆ live objects` (no dangling root) | manual over `cache_eviction_plan_v1` + GC roots | — |
| T-HA1 **Hash agility** | `decode(tagged digest) = none for unknown tag → lookup = Miss`; `tag ≠ tag' → key ≠ key'` | generated (tags from the kind registry) | `verified_cas_kind_registry_v1` |
| T-ND1 **Nondeterminism quarantine** | `same action_digest ∧ different mapping → Err CacheNondeterminism ∧ no overwrite` — already true of `cache_writer_v1`; theorem states it and a second instance *fails* for the workspace path until it gets a journal | manual | — |
| T-GS1 **Generic instance key** (promote F6) | K1/K2 as Lean theorems over `MType` (structural key injective on closed types); S1–S3 as lemmas | manual, replacing bounded-exhaustive | F6 |

### 4.2 Theorem-count accounting the gate must enforce

The F1 gate rule "KEY-field count + 1 == `*_change_visible` count" is the right
shape. Extend it to: (a) **live** key fields (§2.0 item 1 and 2) — not the
shadow `ActionKey`; (b) one `*_read_edge` theorem per `read_kind`; (c) an
explicit **`known_gaps:`** list in the schema, each entry naming a §2.2 row,
with the gate requiring `|gaps| + |visible| + |read_edge| == |inputs|`. A gap
can only be *removed* by adding a theorem; it can never be added silently.

### 4.3 Correspondence to the Simple code (keeping model and code in sync)

Follow the two patterns already in the tree:

1. **Generated layer** (as F1/F9): `gen_cache_model/main.spl` emits
   `Generated/Model.lean`, `FieldTheorems.lean`, `Golden.lean` *and* the Simple
   encoder `generated/action_key_v2.spl`. Extend the schema with the live key's
   fields (`native_build_cache_scope_key`, `CompileOptionsHash`, env identity,
   `DependencyEntry`) so the **same generator** emits the Simple composition the
   driver calls. Today the driver hand-writes those strings (`incremental.spl:497,583`;
   `compile_options_hash.spl:112-176`); that is the divergence that makes F1 a
   shadow proof. Regeneration byte-identity (gate step 4) then pins code to model.
2. **Manual constraints layer** (as F9's `GENERATED_CONTRACT.md` and F3's
   `source_bindings.json`): `Theorems/*.lean` never regenerated; each manual
   theorem names the Simple function and the commit it mirrors; a
   `check-cache-formal-source-binding.shs` compares the pinned
   `sha256(fn body)` of each bound Simple function against the binding file and
   **fails** when the code moved without the proof being re-reviewed — the
   mechanism F3's header asks for ("Replay must separately call the pinned Simple
   functions") but nothing runs.
3. **Golden vectors both ways**: Simple computes the vector, Lean re-derives it
   at `lake build` (F1 step 3); add the live-key vectors and the `.rr`
   forward/reverse pair.
4. **Bounded-exhaustive twins** (F6/F7 style) for every manual theorem, under
   `test/00_formal_verification/compiler/`, so a developer without `lake` still
   gets a red test when the model breaks.

### 4.4 CI gating

| Gate | Tier | Why |
|---|---|---|
| `check-cache-protocol-formal.shs` (exists) | `bootstrap` row in `must_check_gates.sdn` + required-gates extended CI job | `lake` is not on push hosts (the script correctly answers ERROR exit 2, never PASS, when it is absent), so it cannot be a push-tier row; the extended job can install `elan`. Today it runs **nowhere**. |
| `check-lean-proofs.shs --project src/verification/build_cache` + `cache_identity` + `cache_protocol` | same | iterates every Lake project; scope it so the cache projects are named rows |
| `check-cache-formal-source-binding.shs` (new, §4.3.2) | `push` (text-only, fail-closed, <2 s) | the one check that can run on every push: it needs no Lean, only hashes of bound Simple function bodies |
| bounded twins under `test/00_formal_verification/compiler/` | ordinary `bin/simple test` | already how F6/F7 run |
| F1 regeneration byte-identity | already in `check-cache-protocol-formal.shs` step 4 | keeps generated Simple encoder == generated Lean model |

### 4.5 Order of work

1. Move the live key composition into the schema + generator (§4.3.1); wire the
   driver to the generated encoder. This alone makes F1/F2 apply to the real key.
2. Add `known_gaps:` with the §2.2 rows and the counting rule (§4.2); wire both
   Lean gates into `must_check_gates.sdn` (§4.4). The gate goes red honestly.
3. Retarget F3 to the #4372 leader/waiter table (T-SF1), implementing re-drive
   as the fix the failing proof demands.
4. T-RR1 with a bounded twin; T-RG1 over `package_tldr_early_cutoff_v1`.
5. Close §2.2 rows in key-visibility order: CTFE env (one-line populate),
   linker sha + link order, `src/lib` fingerprint, GuardId, impl-set digest,
   inline body digest, advice-body weave root.

---

## 5. Non-goals

Promotion/attestation theorems (F8 "Promotion safety") are out of scope: main
promotion is not part of the per-file build on `release/1.0.0`. No theorem here
claims anything about the Rust seed's `object_cache_key` (`native_project/mod.rs`),
which is bootstrap-only.
