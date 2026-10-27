> Retained smaller-model audit, reviewed as input to the integrated plan. Current refresh: `d8ead19f9ff8820d1acfe7e2a9b01e59827bc465`. Earlier `71e996` findings/missing-plan notes below are historical and superseded by the refresh. No runtime tests executed.

# SCV compiler / TLDR / cache / runner audit (refreshed)

## Revision and audit history

- First read-only pass: `/tmp/simple-scv-phase2-plan-design-20261027` at `71e9962598f` (2026-10-27); the named plan had not yet arrived, so that pass correctly recorded a missing-plan limitation and source-only findings.
- Refresh: same worktree synchronized and clean at `d8ead19f9ff8820d1acfe7e2a9b01e59827bc465`. Compared only the prior audit's relevant source scope and plan/tests added or changed since `71e9962598f`; no build/test run.
- The supplied plan now exists at `doc/03_plan/app/tools/simple_scv_compiler_tldr_build_cache_implementation_plan_2026-10-27.md` (P0–P10 §§15; SCV-CACHE-01–28 §16). Its companion named in the header was not found at `doc/03_plan/app/tools/` during this pass. This is an implementation/source audit, not runtime verification.

## Existing source owners and revision delta

- **SCV snapshot remains V1.** `src/lib/scv/compile_snapshot.spl:49-60,688-705` defines `ScvCompileSnapshotV1` and `scv_compile_snapshot_acquire_v1(root, cache_root, source_roots)`. It snapshots rows from the published compile-source inventory, raw bytes and SHA-256, only permits `build/scv` or `.simple/scv` cache roots, and validates opened provenance/inventory/receipt before reuse (`:713-845`). Since the earlier audit, it adds touch/LRU retention (`:827-832,890-961`) and removes `.used` on explicit cleanup (`:963-979`). Still no `ScvSnapshotV2`, worktree/editor/generated/external/config overlays, capture epoch/coverage, exact diff API, directory inventory root, or SCV validation receipt.
- Existing snapshot callers still consume V1 (`src/app/bootstrap_builder/native_group_phase2_scv.spl`, `native_group_index_build.spl`, `src/app/compiler_entrypoint/source_authority.spl`). There is no V2 adapter or migration in these audited paths. Package module index schema V1–V4 remains intact; V3 is still supported as the scoped entry-closure format (`src/compiler/80.driver/cache/package_module_index.spl:31-70,386-410,482-583`). V4's generated-source digest is not a source snapshot/read-set receipt.
- **Frontend cache collision hardening changed.** `frontend.spl` now computes one native SHA-256 of exact parse source and passes it to SPAB/FPC load/store (`src/compiler/10.frontend/frontend.spl:136-159,179-208`); cache load/store reject absent identity and require stored source identity to equal caller (`frontend_parse_cache.spl:150-199,219-265`). `frontend_parse_cache_scope()` additionally folds `SIMPLE_HIR_CFG_SELECT` into a published scope (`frontend_parse_cache.spl:98-112`). This is stronger source/cache identity, not complete build input/read-set verification.
- **TLDR import prototype added behind a real default-off flag.** `SIMPLE_TLDR_IMPORTS=1` is read/memoized by `driver_tldr_import_route_v1.spl:29-50`; source comments define summary-only imports/fallback behavior (`:1-10`). `tldr_summary_v1.spl` creates line-scanned, source-digest-validated summary rows, single-flight/lease publication (`:285-312`); `module_surface_from_tldr_v1.spl:1-19,52-143` reconstructs a `ModuleSurface` from an interface stub and fails closed on fallback/unsupported rows or missing function return type. However, bounded source search finds `tldr_route_worker_v1` and `driver_register_tldr_surfaces_v1` definitions but no production source caller; current references are tests. Meanwhile native-build and closure walkers reject closure routes when the flag is enabled (`native_build_main.spl:826-833,1999-2007`; `driver_source_pipeline_parsing.spl:799-801,1012-1014`). Thus the new flag is genuine but the end-to-end import route is not yet shown wired; do not characterize imports as production-admitted from these sources alone.
- `CompileContext.tldr_entry_only/tldr_imports` remain default false/empty (`driver_types.spl:536-544`); HIR lowering copies them and gates HIR closure digest (`driver_hir_pipeline_lowering.spl:1049-1088,1812-1825`; `driver_cache_scope_policy_v1.spl:26-30`). Existing `PublicSummaryV1` and `ModuleSurface` remain distinct owners; summary stub is an interface projection, not a compiler lowering replacement.
- **Semantic cache/graph support exists independently of SCV.** HIR cache keys source, compiler scope, full frozen surface closure and lowering flags (`driver_hir_cache.spl:10-26,140-203`). Compiler cache modules also contain semantic query read manifests, reverse projections and transactional reference-generation code. These do not establish that `ScvCompileSnapshotV1` captures or verifies those actual reads against a new snapshot.
- **TaskRunner remains scheduler owner.** `src/lib/common/task_runner/scheduler.spl:1-25,42-69` owns validated DAG and readiness. No new SCV snapshot subscription/verification adapter for BuildRunner/TestRunner was found in the scoped diff.

## P0–P10 status against plan §15

| Phase | Source-backed status | Gap / evidence limit |
|---|---|---|
| P0 audit | **Done for this lane:** V1 callers, index schema V1–V4, compiler/TLDR/cache and tests inventoried here. | Not a full repo-wide SDN/gateway/journal audit; supplied companion plan absent. |
| P1 Snapshot V2 / overlays / barrier / identities | **Not implemented in audited SCV compile snapshot.** V1 only. | Dirty worktree byte drift is observed during materialization, but editor/generated/external/config overlays and one coherent capture barrier/coverage are absent. |
| P2 exact cross-snapshot deltas / Unknown reconciliation | **Not found.** | Existing source inventory/snapshot identity is not a file+directory pairwise delta or event-overflow reconciliation API. |
| P3 positive/negative resolution witnesses | **Partial outside SCV.** TLDR import helper maps modules from supplied paths; other compiler semantic-query manifests include reads/negative witness concepts. | No SCV `resolve_path`/directory witness bound to the TLDR route; missing import/new member invalidation is not proven. |
| P4 manifest verification / snapshot receipt | **Partial outside SCV.** Existing cache has semantic read manifests, action generations and receipts. | No evidence that an existing artifact's recorded reads are verified against the requested V1/V2 snapshot or that unchanged semantic artifacts receive a new exact snapshot validation receipt. Cross-commit reuse remains gated off by plan. |
| P5 directory/AOP old+new scope | **Partial compiler owners only.** Existing AOP match cache and directory/TLDR related mechanisms exist. | No SCV changed-directory feed or old/new match-universe receipt demonstrated. |
| P6 macro/generic forward-use transaction | **Partial compiler/cache owners.** Generic TLDR tables and atomic reverse-reference generation exist. | New TLDR source does not demonstrate SCV-coordinated forward-manifest replacement for macro/generic use or stale-worker admission. |
| P7 AST-set/SCC/Bloom/path-hash | **Partial.** Package module graph/index and SCC schedulers exist; TLDR helper and flag are new. | No SCV AST/HIR/MIR immutable set roots or complete Bloom+directory proof; TLDR route has no production caller in scoped search. |
| P8 tagged aliases / cross-process containers / pinning | **Partial unrelated cache infrastructure.** Digest types/CAS and cache gateway/container mechanisms exist. | No SCV-owned alias registry plus exact container resolver/pins satisfying plan's end-to-end cross-process pack contract. |
| P9 SCV/BuildRunner/TestRunner admission | **Partial shared scheduler only.** Common TaskRunner remains authoritative. | No common frozen-snapshot/read-receipt adapter proving embedded, BuildRunner, and TestRunner equivalence. |
| P10 retention/crash/compatibility | **Partial.** New SCV compile snapshot max-count/LRU/min-age eviction in V1 (`compile_snapshot.spl:890-961`); package index V1–V4 readers unchanged. | Retention does not model protected branches/releases/worktrees/active cross-process pins; no full SCV journal crash replay or semantic-key shadow migration evidenced. |

## SCV-CACHE-01–28 gap map (plan §16)

Status labels refer to source/test evidence only. Test anchors are not claims that tests ran.

| ID | Current evidence / disposition |
|---|---|
| 01 no-op same output | Frontend/HIR cache-hit tests exist, but no evidence of zero parser/codegen/link work **and** no output rewrite on verified SCV receipt. Gap. |
| 02 deleted destination materialization | No audited SCV/cache hit-to-destination materializer oracle. Gap. |
| 03 unrelated commit/branch reuse + new receipt | V1 content-addressed snapshot reuse only for exact inventory; no semantic cross-snapshot receipt. Gap. |
| 04 dirty worktree/editor | V1 rereads/hashes source and has drift handling; no editor overlay or stale semantic artifact test. Partial. |
| 05 concurrent edit/barrier | No freeze/admission barrier API or acknowledged-edit test. Gap. |
| 06 lost events/unknown coverage | No SCV Unknown coverage reconciliation found. Gap. |
| 07 merge/non-ancestor branch switch | No exact SCV cross-snapshot diff API. Gap. |
| 08 rename/AOP directory scope | Path safety and AOP owner mechanisms exist separately; no old/new SCV directory fact proof. Gap. |
| 09 previously missing import appears | TLDR route detects unresolved module on current invocation, but no negative witness ties old absence to later addition. Gap. |
| 10 pointcut old/new match universe | AOP cache exists; no SCV candidate-universe invalidation evidence. Gap. |
| 11 behavior-only advice changes layout | No SCV/TLDR cache test proving rejection of invalid interface. Gap. |
| 12 macro interface/body nested users | Existing macro cache/reverse manifests are separate; no TLDR/SCV nested-user replacement proof. Partial. |
| 13 generic use demand mutations | Generic caches/read tables exist; no SCV transactional demand/pin oracle. Partial. |
| 14 failed/cancelled/stale replacement | Atomic reverse-reference generation and cache publication tests exist separately; not SCV manifest replacement integration. Partial. |
| 15 AST-set SCC/new file | Package module graph and SCC scheduler exist; no immutable SCV set-root/new-directory proof. Partial. |
| 16 forced short-ID collision | `test/01_unit/compiler/driver/cache_xxh3_identity_gate_spec.spl` and exact SHA parse identity harden cache admission; no SCV path-ID collision oracle. Partial. |
| 17 multiple digest alias/corrupt remote | Verified CAS/digest infrastructure exists; no SCV multi-alias remote corruption scenario. Partial. |
| 18 endian/targets | HIR target-neutral key/target tests and fixtures added (`hir_cache_key_neutral_spec`, `hir_cache_key_target_spec`); no big-endian simulation or full AST/HIR/OBJ matrix. Partial. |
| 19 new process packed refs | Parse/HIR hit-across-process tests exist; no packed external container-ID pointer reconstruction/pin scenario. Partial. |
| 20 crash during publication | Atomic publication tests exist for specific cache owners; not SCV manifest/index/receipt root replay. Partial. |
| 21 embedded vs BuildRunner | No same frozen snapshot + semantic output/read-set equivalence evidence found. Gap. |
| 22 TestRunner env/input | Shared TaskRunner exists, but no proof OBJ reuse while rerunning changed test env/data. Gap. |
| 23 eviction under protected refs | V1 snapshots now LRU count/age bounded, but policy has no protected ref/worktree/active pack roots. Partial. |
| 24 V1–V4 migration/new semantic key | Package index V1–V4 readers remain; `phase2_phase3_compatibility_manifest_spec.spl` added/updated. No cross-commit complete-witness admission. Partial. |
| 25 100 concurrent TLDR consumers | TLDR single-flight + lease/wait logic exists; unit tests cover summary/route helpers, not 100 consumers with no lost wakeups and exact reverse manifest. Partial. |
| 26 generated source changes directory inventory | TLDR summary may process source; no source-generation feedback suppression/inventory-generation test. Gap. |
| 27 symlink/case/Unicode/policy | V1 path/containment checks and host path utilities exist; no canonical path policy + search-domain witness change test. Partial. |
| 28 clean build oracle after facet invalidation | ModuleSurface-from-TLDR tests compare projections/digests; no full cold/warm symbol/layout/runtime oracle and stage counts after partial invalidation. Gap. |

## Test anchors observed (not executed)

- New parse identity / config neutrality: `test/01_unit/compiler/driver/cache_xxh3_identity_gate_spec.spl`, `test/01_unit/compiler/80.driver/hir_cache_key_neutral_spec.spl`, `test/01_unit/compiler/80.driver/hir_cfg_select_flag_cache_key_spec.spl`, `test/01_unit/compiler/driver/hir_cache_key_target_spec.spl`, `test/01_unit/compiler/driver/hir_cache_hit_across_processes_spec.spl`.
- New TLDR route/summary/surface: `test/01_unit/compiler/driver/tldr_route_spec.spl:84-124,152-258`, `tldr_summary_spec.spl:25-62,90-134`, `module_surface_from_tldr_spec.spl:26-90,134-169`. These directly cover flag parsing/guard/helper behavior and projections, not production caller wiring.
- Snapshot retention: `test/01_unit/lib/scv/compile_snapshot_retention_spec.spl`. Existing snapshot tests still exercise inventory/materialization/reuse; no overlay/negative-read tests were found in the scoped changed set.
- Compatibility: `test/02_integration/compiler/cache/phase2_phase3_compatibility_manifest_spec.spl`; package index V1–V4 implementation remains in `package_module_index.spl`.

## Review conclusion

The update materially advances **parse-source identity (A-2), HIR key neutral/target handling, V1 snapshot retention, TLDR summary generation, ModuleSurface reconstruction, and a feature-gated TLDR import prototype**. It does not close the central SCV plan gate: a V1 compile-source snapshot SHA/tree is not an overlay/config/directory/negative-witness proof; existing compiler semantic manifests are not yet shown verified by SCV against the requested snapshot. Keep semantic lowering in compiler owners and scheduling in common TaskRunner. Preserve package index schema 3 and V1–V4 reader behavior during migration. `SIMPLE_TLDR_IMPORTS` is present and default-off, but production route wiring remains unproven by caller search, so do not enable it as a completed route based on these source artifacts.
