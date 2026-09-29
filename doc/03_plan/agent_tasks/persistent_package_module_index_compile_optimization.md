# Persistent Package/Module Index Compile Optimization — Agent Tasks

Status date: 2026-09-02

## Audit rules

- Scope is the 44 scenarios in `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`.
- `implemented` means the production compile path satisfies the complete scenario, not merely that a helper exists.
- `partial` means a production primitive exists, but integration, admission, or one required invariant is absent.
- `missing` means no production implementation presently owns the required behavior.
- The SPipe checker `scripts/check/check-persistent-smf-package-index.shs` is absent. Therefore no row has executable end-to-end production evidence yet.
- Do not edit or duplicate the active package-index lane (`src/compiler/80.driver/cache/package_module_index.spl`) or active SCV lane (`src/lib/scv/compile_snapshot.spl` and its current native-build integration).

## Current production owners

| Owner | Current write set | Authority |
|---|---|---|
| Active index lane — Peirce (`01a0612a-bf0c-75d1-849d-a2294e10dbe6`) | `src/compiler/80.driver/cache/package_module_index.spl` | Immutable index generation, validation, atomic `CURRENT`, reverse edges, invalidation primitive, deterministic acyclic package order |
| Active SCV lane (`01a06138-bb96-7cb2-84f4-c8bb816c5e64`) | `src/lib/scv/compile_snapshot.spl`, current SCV edits in `src/app/io/_CliCompile/native_build_closure.spl` | Immutable compile snapshot and transparent native-build freeze |
| Existing driver/cache owner | `src/compiler/10.frontend/frontend_parse_cache.spl`, `src/compiler/80.driver/driver_source_loading.spl`, `src/app/io/_CliCompile/native_build_closure.spl` | Existing source-based entry closure and parse/native cache; not package-index authority |
| Existing SMF owner | `src/compiler/80.driver/smf_serialization.spl`, `src/compiler/80.driver/smf_writer.spl`, `src/compiler/80.driver/watcher/smf_manifest.spl` | General SMF serialization and manifest parsing; no `PackageTldrHeaderV1`/section-demand package API |
| Existing daemon owner | `src/compiler/80.driver/watcher/watcher_daemon.spl` | Long-lived process support; no pinned package-index generation per request |

## Exact 44-scenario matrix

| # | Scenario key | Status | Current production evidence | Owning/gap lane |
|---:|---|---|---|---|
| 1 | `explicit-closure-only` | partial | `native_build_closure.spl` resolves entry imports, but `driver_source_loading.spl` remains source-scan based and does not consume the persistent index. | INT |
| 2 | `unrelated-tree-unreadable` | missing | No index-only discovery path proves unrelated trees are never opened. | INT |
| 3 | `header-metadata-reuse` | partial | Frontend parse cache and general SMF support exist; no admitted package export-header consumer bypasses dependency bodies. | META, INT |
| 4 | `metadata-section-lazy-read` | partial | SMF readers exist, but no `PackageTldrHeaderV1` section directory or demanded-section API exists. | META |
| 5 | `package-archive-cache-hit` | missing | No `PackageArchiveReceiptV1`, canonical package archive store, member admission, or action-key lookup exists. | CACHE |
| 6 | `missing-index-denied` | partial | `package_module_index_read_current_v1` fails closed; compile entrypoints do not call it. | Active index, INT |
| 7 | `direct-reverse-invalidation` | partial | `package_module_index_invalidate_changes_v1` walks direct reverse edges, but no compile planner consumes the result. | Active index, PLAN |
| 8 | `indirect-reverse-invalidation` | partial | The index primitive walks reverse edges transitively; no end-to-end rebuild/publication path exists. | Active index, PLAN |
| 9 | `generated-source-invalidation` | partial | Generated inputs exist elsewhere in the driver, but producer input/output digests are not package-index/action authority. | GEN |
| 10 | `config-variant-isolation` | partial | Existing compile caches include configuration inputs, but index entries lack canonical `ConfigVariantKeyV1`. | META |
| 11 | `build-tag-variant-isolation` | missing | No package-index build-tag variant identity or admission boundary exists. | META |
| 12 | `private-body-export-early-cutoff` | partial | `PackageModuleChangeV1` distinguishes content from exported semantics; no producer compile compares/publishes semantic digests to cut off dependents. | Active index, PLAN |
| 13 | `generated-output-undeclared-denied` | missing | No declared-output set is enforced before generated package publication. | GEN |
| 14 | `deterministic-independent-schedule` | partial | `package_module_index_schedule_packages_v1` emits deterministic serial order; no parallel owner-result scheduler/commit layer exists. | Active index, PLAN |
| 15 | `scc-group-invalidation` | missing | Current scheduler explicitly returns `package-cycle-requires-scc-authority`; no SCC transaction exists. | PLAN |
| 16 | `daemon-warm-reuse` | partial | A watcher daemon and frontend caches exist, but no admitted package state/archive generation is retained and pinned. | DAEMON |
| 17 | `clean-warm-reproducibility` | partial | Existing native/parse caches provide reusable artifacts, but package metadata/archive byte identity is neither implemented nor compared. | CACHE, REPRO |
| 18 | `missing-index-bounded-rebuild` | missing | No separate explicitly authorized bounded-reindex operation exists. | INDEXER |
| 19 | `stale-index-denied` | partial | Index schema/digests are validated, but admission cannot compare producer/root/variant expectations supplied by a compile request. | Active index, INDEXER |
| 20 | `tampered-index-denied` | partial | Immutable generation digest and `CURRENT` pointer checks exist; entrypoints do not enforce them. | Active index, INT |
| 21 | `corrupt-metadata-denied` | partial | Index entry digests and graph shape are validated, but package metadata/archive admission does not exist. | META, CACHE |
| 22 | `crash-before-publish` | partial | Immutable index file plus temporary `CURRENT` rename preserves the prior pointer; full metadata/action/archive transaction is absent. | Active index, STORE |
| 23 | `crash-after-publish` | partial | Index pointer publication is atomic, but no one-generation transaction covers all package artifacts and receipts. | Active index, STORE |
| 24 | `no-hidden-full-scan-fallback` | partial | The index module itself never scans; production entrypoints still use source scanning. | INT |
| 25 | `scv-snapshot-bound-build` | partial | `scv_compile_snapshot_acquire_v1` and native-build freeze exist, but package actions are not created from the snapshot-bound index. | Active SCV, INT |
| 26 | `scv-concurrent-worktree-edit-isolated` | partial | Frozen files are materialized and native-build paths are rewritten; all compile modes and package publications are not bound. | Active SCV, INT |
| 27 | `scv-source-drift-new-build` | partial | Drift is detected and reported, but distinct scheduled build/action identity is not implemented. | Active SCV, PLAN |
| 28 | `scv-snapshot-create-crash` | partial | Staging rename and recovery of `.tmp.*` exist; crash injection/admission evidence is absent. | Active SCV, STORE |
| 29 | `scv-snapshot-cleanup-crash` | partial | Recovery removes staging snapshots, but no lease/pin prevents cleanup of active generations. | Active SCV, STORE, DAEMON |
| 30 | `scv-provenance-binding` | partial | Snapshot provenance fields exist in index/action digests; no package action/archive receipt completes the binding chain. | Active SCV, Active index, CACHE |
| 31 | `scv-no-live-worktree-fallback` | partial | Native entry closure rewrites to the frozen root and fails closed locally; other entrypoints remain unbound. | Active SCV, INT |
| 32 | `scv-implicit-compile-quiet` | partial | Native entry-closure implicitly acquires a snapshot; normal compile/check/MCP/LSP paths are not uniformly covered. | Active SCV, INT |
| 33 | `scv-git-event-auto-index-update` | missing | No Git/SCV event observer updates package metadata automatically. | EVENT |
| 34 | `scv-internal-write-boundary` | partial | Snapshot code writes below caller-provided `build/scv`; no centralized path-policy/admission receipt covers all package cache writes. | Active SCV, STORE |
| 35 | `comment-only-semantic-reuse` | partial | Content-only invalidation avoids reverse dependents when semantic flags are false; no parser/export evidence computes those flags. | Active index, META, PLAN |
| 36 | `whitespace-only-semantic-reuse` | partial | Same primitive as row 35; no canonical semantic digest producer is wired. | Active index, META, PLAN |
| 37 | `scv-git-state-nonmutation` | partial | Current SCV implementation contains no Git mutation API, but no cross-entrypoint audit/receipt proves the invariant. | Active SCV, EVENT, INT |
| 38 | `scv-concise-failure-diagnostics` | partial | Native freeze emits bounded `SCV-E-*`/`SCV-W-*` messages; package-index errors and other entrypoints are not unified. | Active SCV, INT |
| 39 | `scv-internal-metadata-atomic-gc` | partial | Snapshot/index atomic renames exist independently; generation leases, complete transaction publication, and safe GC do not. | STORE, DAEMON |
| 40 | `daemon-generation-workspace-isolation` | missing | No per-request package generation pin/release or cross-workspace state key exists. | DAEMON |
| 41 | `remote-cache-local-admission` | missing | No remote package action/archive client or hostile-content local admission exists. | REMOTE |
| 42 | `remote-cache-poison-denied` | missing | No remote cache boundary exists. | REMOTE |
| 43 | `cross-mode-reproducibility` | missing | No canonical package evidence comparison across worker count, daemon restart, checkout root, and local/remote modes exists. | REPRO |
| 44 | `entrypoint-no-scan-matrix` | missing | Compile, check, bootstrap, MCP, LSP, daemon startup, and daemon request do not share one index-only owner. | INT |

Summary: **0 implemented, 32 partial, 12 missing**. This is an implementation audit, not a claim that the supporting primitives are correct or verified.

## Disjoint parallel write sets

All lanes are additive and must not edit another lane's paths. Shared integration files are reserved to `MERGE` only. Each lane returns immutable result values; only `MERGE` publishes cross-lane state.

| Lane | Scenario rows | Exclusive write set | Required output |
|---|---|---|---|
| ACTIVE-INDEX (already active; do not duplicate) | 6–8, 12, 14, 19–24, 30, 35–36 | `src/compiler/80.driver/cache/package_module_index.spl` | Finish its existing lane; no new agent assignment |
| ACTIVE-SCV (already active; do not duplicate) | 25–32, 34, 37–38 | `src/lib/scv/compile_snapshot.spl`; currently owned SCV portions of `src/app/io/_CliCompile/native_build_closure.spl` | Finish its existing lane; no new agent assignment |
| META | 3–4, 10–12, 21, 35–36 | `src/compiler/80.driver/cache/package_metadata.spl`, `src/compiler/80.driver/cache/package_variant_key.spl` | `PackageTldrHeaderV1`, `PackageExportSmfV1`, demanded-section admission, semantic/variant digests |
| CACHE | 5, 17, 21, 30 | `src/compiler/80.driver/cache/package_action_cache.spl`, `src/compiler/80.driver/cache/package_archive_store.spl` | `PackageActionKeyV1`, `PackageArchiveReceiptV1`, local archive/member admission |
| PLAN | 7–8, 12, 14–15, 27, 35–36 | `src/compiler/80.driver/cache/package_compile_plan.spl`, `src/compiler/80.driver/cache/package_compile_scheduler.spl` | `PackageCompilePlanV1`, SCC grouping, deterministic owner-result parallel schedule, early cutoff |
| GEN | 9, 13 | `src/compiler/80.driver/cache/package_generated_inputs.spl` | Declared generator inputs/outputs, producer digests, deny-before-publish |
| INDEXER | 18–19 | `src/compiler/80.driver/cache/package_index_builder.spl` | Explicit bounded rebuild command core; expected-producer/root/variant admission inputs; never invoked as fallback |
| STORE | 22–23, 28–29, 34, 39 | `src/compiler/80.driver/cache/package_generation_store.spl` | Atomic complete-generation transaction, leases, orphan recovery, safe GC, owned-write policy |
| EVENT | 33, 37 | `src/lib/scv/compile_event_index.spl` | Read-only Git/SCV event observation and automatic dirty-set update; no index/ref/lock/history mutation |
| DAEMON | 16, 29, 39–40 | `src/compiler/80.driver/watcher/package_index_session.spl` | Per-request generation/workspace pin, warm state, release/refresh boundary |
| REMOTE | 41–42 | `src/compiler/80.driver/cache/package_remote_cache.spl` | Hostile remote content fetch result plus complete local admission; no graph/generation authority |
| REPRO | 17, 43 | `src/compiler/80.driver/cache/package_reproducibility.spl` | Canonical evidence/digest comparison across supported modes |
| INT | 1–2, 6, 20, 24–27, 30–32, 37–38, 44 | Reserved existing callsites listed below | Wire one catalog/plan owner after all provider lanes merge; remove scan fallback and unrelated reads |
| SPIPE | all 44 | `scripts/check/check-persistent-smf-package-index.shs` only | Real production checker; no simulation/hardcoded scenario output |

### `INT` reserved integration files

Only the merge owner may edit these after provider APIs are accepted:

- `src/app/io/_CliCompile/native_build_closure.spl`
- `src/compiler/80.driver/driver_source_loading.spl`
- `src/compiler/80.driver/watcher/watcher_daemon.spl`
- compile/check/bootstrap dispatch files under `src/app/cli/`
- MCP and LSP compile/request adapters under `src/app/mcp/` and `src/app/simple_lsp_mcp/`

If an adapter can be added as a new file, the lane must add only that file and leave imports/dispatch changes to `MERGE`.

## Shared interface freeze

Provider lanes must target these names and may not invent competing models:

- `PersistentSmfPackageIndexV1` (implemented physically by the active index lane's `PackageModuleIndexGenerationV1` until merge-owner rename/adaptation)
- `PackageTldrHeaderV1`
- `PackageExportSmfV1`
- `ConfigVariantKeyV1`
- `PackageActionKeyV1`
- `PackageArchiveReceiptV1`
- `PackageCompilePlanV1`
- `PackageCompileResultV1`
- `ScvCompileSnapshotV1`

SPipe helper flow names remain exactly the 44 `--scenario` keys in the executable spec. Any not-yet-wired checker branch must fail fast with `fail(...)` or a nonzero `PKG-IDX-*` result; placeholder PASS output is forbidden.

## Merge and review ownership

- **Merge owner (`MERGE`)**: primary normal/highest-capability Codex agent. It alone resolves shared types, updates active index/SCV files after their owners hand off, edits reserved integration callsites, and runs the focused 44-scenario gate once.
- **Final reviewer**: a fresh normal/highest-capability agent that did not implement or merge any lane. It audits all 44 rows, write-set compliance, zero recursive fallback, SPipe authenticity, deterministic reproduction, and source/Git nonmutation.
- **Lower-model sidecars**: `N/A` for production writes. They may perform read-only search, but broad findings and every done mark require the final reviewer.
- A lane is not mergeable if it edits another lane's write set, changes the executable SPipe scenario contract, emits simulated evidence, or introduces a second index/closure authority.
