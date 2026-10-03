# Item 6 compile optimization acceptance audit (2026-10-03)

Base: `7d16ab11d2227cbe5f29dc998b76a1eff326abbb`, target `release/1.0`.
Owner: `/root/item6_acceptance`, isolated `work/item6-acceptance-20261003`.
This appendix refines existing selected PSI requirements; it selects no new requirements.

## Evidence quality and current status

The canonical system specification contains 44 scenarios with explicit `step()` actions and assertions, but its invoked `scripts/check/check-persistent-smf-package-index.shs` is absent at the base. These are unverified acceptance contracts, not passing system coverage. No production receipt adapter may print predetermined observations to satisfy them. A missing checker is structural RED evidence, not an executed behavioral red test.

`package_module_index_spec.spl` imports production code and covers stale compare-and-swap publication, canonical roundtrip, and precise content/export invalidation. `package_index_route_spec.spl` imports production routing for selected scope, variants, missing authority, and corrupt decode cases. These tests are real but cannot establish all system contracts. Their execution in this session remains blocked pending an admitted self-hosted runtime.

`package_index_driver_cutover_contract_test.shs` greps implementation strings; its PASS would establish source shape only. It must not count toward source-open, invalidation, atomicity, cache reuse, or no-scan acceptance. Existing manual step vocabulary is modern; do not replace it with legacy Given_/When_/Then_ helpers.

## Concrete canonical acceptance list

Each row requires the named production scenario, status 0, empty unexpected stderr, and the listed observations from actual compiler state/receipts. All rows remain **UNVERIFIED**. The original audit found the checker absent; the implementation update below records the subsequently added owner adapters. For error scenarios, checker success means the compiler operation was actually refused with the specified reason; it never means compilation succeeded. Instrumented reads, counters, and digests must originate at production owners, not a test-side graph model.

| Requirement | Scenario | Required production observations |
|---|---|---|
| `PSI-REQ-001` | `explicit-closure-only` | `requested=app`; `resolved_closure=model,api,util,app`; `compiled=model,api,util,app`; `recursive_scan_count=0` |
| `PSI-REQ-001` | `unrelated-tree-unreadable` | `result=success`; `unrelated_tree=unreadable`; `unrelated_read_count=0`; `recursive_scan_count=0` |
| `PSI-REQ-001` | `header-metadata-reuse` | `metadata_kind=PackageTldrHeaderV1`; `header_cache_hits=model,api,util`; `dependency_source_body_reads=0`; `export_abi_digest_match=true`; `smf_sections_read=demanded-only` |
| `PSI-REQ-001` | `metadata-section-lazy-read` | `tldr_headers_read=model,api,util,app`; `smf_sections_read=demanded-only`; `unreached_metadata_read_count=0`; `dependency_source_body_reads=0` |
| `PSI-REQ-001` | `package-archive-cache-hit` | `archive_receipt_kind=PackageArchiveReceiptV1`; `archive_cache_hits=model,api,util`; `dependency_recompile_count=0`; `archive_variant_digest_match=true`; `action_key_match=true`; `archive_member_payloads_match=true` |
| `PSI-REQ-001` | `missing-index-denied` | `observed_error=PKG-IDX-001`; `compile_started=false`; `fallback_scan_count=0` |
| `PSI-REQ-002` | `direct-reverse-invalidation` | `edited=util`; `invalidated=util,app`; `compiled=util,app`; `retained=model,api` |
| `PSI-REQ-002` | `indirect-reverse-invalidation` | `edited=model`; `invalidated=model,api,util,app`; `compiled=model,api,util,app`; `unrelated_read_count=0` |
| `PSI-REQ-002` | `generated-source-invalidation` | `generated_identity_bound=true`; `invalidated=generated_api,generated_app`; `producer_digest_match=true`; `unchanged_generated_archive_reused=true` |
| `PSI-REQ-002` | `config-variant-isolation` | `changed_variant=debug`; `invalidated_variant=debug`; `retained_variant=release`; `cross_variant_reuse=false` |
| `PSI-REQ-002` | `build-tag-variant-isolation` | `changed_build_tag=feature_x`; `retained_build_tag=feature_y`; `variant_key_kind=ConfigVariantKeyV1`; `cross_variant_reuse=false` |
| `PSI-REQ-002` | `private-body-export-early-cutoff` | `producer_action_changed=true`; `producer_archive_changed=true`; `export_digest_changed=false`; `reverse_propagation_stopped=true`; `consumer_recompile_count=0` |
| `PSI-REQ-002` | `generated-output-undeclared-denied` | `observed_error=PKG-IDX-004`; `generated_output_admitted=false`; `index_publish_count=0`; `cache_publish_count=0` |
| `PSI-REQ-003` | `deterministic-independent-schedule` | `ready_set=alpha,beta`; `dispatch_order=alpha,beta`; `commit_order=alpha,beta,bundle`; `repeat_schedule_digest_match=true` |
| `PSI-REQ-003` | `scc-group-invalidation` | `edited=cycle_a`; `invalidated_scc=cycle_a,cycle_b`; `invalidated_reverse=root`; `compiled=cycle_a,cycle_b,root` |
| `PSI-REQ-003` | `daemon-warm-reuse` | `session_receipt_kind=PackageDaemonSessionReceiptV1`; `index_reload_count=0`; `second_request_compile_count=0`; `warm_archive_hits=model,api,util,app` |
| `PSI-REQ-003` | `clean-warm-reproducibility` | `output_digest_match=true`; `header_digest_match=true`; `archive_digest_match=true`; `plan_and_receipt_digest_match=true` |
| `PSI-REQ-004` | `missing-index-bounded-rebuild` | `recovery_policy=bounded`; `manifest_roots_read=1`; `recursive_scan_count=0`; `index_publish=atomic` |
| `PSI-REQ-004` | `stale-index-denied` | `observed_error=PKG-IDX-002`; `compile_started=false`; `recursive_scan_count=0`; `prior_graph_generation_preserved=true` |
| `PSI-REQ-004` | `tampered-index-denied` | `observed_error=PKG-IDX-004`; `compile_started=false`; `recursive_scan_count=0` |
| `PSI-REQ-004` | `corrupt-metadata-denied` | `observed_error=PKG-IDX-003`; `header_consumed=false`; `archive_consumed=false`; `recursive_scan_count=0` |
| `PSI-REQ-004` | `crash-before-publish` | `crash_point=before-publish`; `recovery=previous-valid-generation`; `mixed_generation_observed=false`; `temp_residue_count=0` |
| `PSI-REQ-004` | `crash-after-publish` | `crash_point=after-publish`; `recovery=new-complete-generation`; `mixed_generation_observed=false`; `temp_residue_count=0` |
| `PSI-REQ-004` | `no-hidden-full-scan-fallback` | `fallback_scan_count=0`; `recursive_scan_count=0`; `unrelated_read_count=0`; `receipt_source=production-filesystem-boundary` |
| `PSI-REQ-005` | `scv-snapshot-bound-build` | `snapshot_kind=ScvCompileSnapshotV1`; `inventory_canonical=true`; `inventory_finalized_before_discovery=true`; `action_ids_created_after_snapshot=true`; `source_provider=ScvFrozenSourceProviderV1` |
| `PSI-REQ-005` | `scv-concurrent-worktree-edit-isolated` | `concurrent_worktree_edit=true`; `active_snapshot_mutated=false`; `active_plan_digest_changed=false`; `active_output_digest_matches_frozen_source=true`; `live_worktree_read_count=0` |
| `PSI-REQ-005` | `scv-source-drift-new-build` | `drift_detected=true`; `active_build_mutated=false`; `new_snapshot_revision_distinct=true`; `new_build_id_distinct=true`; `drift_policy_result=rejected-or-new-build` |
| `PSI-REQ-005` | `scv-snapshot-create-crash` | `crash_phase=snapshot-create`; `partial_snapshot_admitted=false`; `previous_snapshot_intact=true`; `orphan_staging_recovered=true` |
| `PSI-REQ-005` | `scv-snapshot-cleanup-crash` | `crash_phase=snapshot-cleanup`; `active_snapshot_deleted=false`; `cleanup_idempotent=true`; `mixed_snapshot_generation_observed=false` |
| `PSI-REQ-005` | `scv-provenance-binding` | `revision_binding_match=true`; `tree_binding_match=true`; `inventory_digest_binding_match=true`; `package_index_action_receipt_binding_match=true`; `provenance_complete=true` |
| `PSI-REQ-005` | `scv-no-live-worktree-fallback` | `observed_error=SCV-BUILD-004`; `live_worktree_fallback=false`; `live_worktree_read_count=0`; `compile_started=false` |
| `PSI-REQ-006` | `scv-implicit-compile-quiet` | `explicit_scv_option=false`; `automatic_snapshot_admitted=true`; `normal_compile_output_lines=0`; `bridge_receipt_kind=ScvCompileBridgeReceiptV1`; `receipt_observable=true` |
| `PSI-REQ-006` | `scv-git-event-auto-index-update` | `event_source=git-or-scv`; `explicit_scv_option=false`; `affected_package_metadata_updated=true`; `unaffected_package_metadata_rewritten=false`; `index_generation_publish=atomic` |
| `PSI-REQ-006` | `scv-internal-write-boundary` | `automatic_write_root=build/scv/compile`; `write_root_ignored=true`; `writes_outside_owned_root=0`; `user_authored_file_writes=0`; `developer_file_timestamp_changes=0` |
| `PSI-REQ-006` | `comment-only-semantic-reuse` | `content_digest_changed=true`; `semantic_export_initializer_provider_digest_changed=false`; `changed_package_reparse_bounded=true`; `dependent_invalidation_count=0`; `dependent_recompile_count=0` |
| `PSI-REQ-006` | `whitespace-only-semantic-reuse` | `content_digest_changed=true`; `semantic_export_initializer_provider_digest_changed=false`; `changed_package_reparse_bounded=true`; `dependent_invalidation_count=0`; `dependent_recompile_count=0` |
| `PSI-REQ-006` | `scv-git-state-nonmutation` | `git_index_digest_match=true`; `git_refs_digest_match=true`; `git_head_match=true`; `git_lock_removed=false`; `history_mutation_command_count=0` |
| `PSI-REQ-006` | `scv-concise-failure-diagnostics` | `success_diagnostic_lines=0`; `failure_diagnostics_concise=true`; `failure_code_present=true`; `receipt_path_present=true` |
| `PSI-REQ-006` | `scv-internal-metadata-atomic-gc` | `metadata_publish=atomic`; `metadata_size_bounded=true`; `ownership_marker_present=true`; `gc_receipt_present=true`; `partial_current_generation=false` |
| `PSI-REQ-007` | `daemon-generation-workspace-isolation` | `generations_observed_per_request=1`; `refresh_during_request=false`; `refresh_between_requests=true`; `workspace_pins_after_close=0`; `workspace_dirty_state_after_close=0` |
| `PSI-REQ-007` | `remote-cache-local-admission` | `remote_content_untrusted=true`; `local_action_admission_complete=true`; `local_archive_member_admission_complete=true`; `remote_graph_authority=false`; `remote_dirty_state_authority=false`; `remote_generation_authority=false` |
| `PSI-REQ-007` | `remote-cache-poison-denied` | `observed_error=PKG-IDX-005`; `remote_content_admitted=false`; `graph_mutation_count=0`; `fallback_scan_count=0`; `recursive_scan_count=0` |
| `PSI-REQ-007` | `cross-mode-reproducibility` | `worker_count_digest_match=true`; `clean_incremental_digest_match=true`; `daemon_restart_digest_match=true`; `checkout_root_cwd_digest_match=true`; `local_remote_digest_match=true` |
| `PSI-REQ-007` | `entrypoint-no-scan-matrix` | `entrypoints=compile,check,bootstrap,mcp,lsp,daemon-startup,daemon-request`; `recursive_scan_count=0`; `unrelated_read_count=0`; `discovery_subprocess_count=0` |

## Focused TDD increments and gaps

1. **PSI-REQ-004 / GC publication exclusion.** Publish A and B using the real persistence API. Select A as CURRENT, hold the same CURRENT.lock used by publication, and attempt collection with B unretained. Collection must fail closed while the lock is held and preserve B's persisted bytes. Release the lock and demonstrate ordinary collection still removes only eligible generations. Runtime lane owns the executable regression and production fix. Capture baseline failure and fixed success using the same admitted self-hosted binary, fixtures, and invocation; source inspection alone cannot provide either result.
2. **PSI-REQ-002 / mixed private and public edits.** Use disjoint dependency pairs `a -> b` and `c -> d` (arrows mean reverse-dependent propagation here). Change only a's body and c's export. Production precise invalidation must return a,c,d and preserve b. Existing module-index unit coverage asserts that lower-level result. The live route still calls `package_module_index_invalidate_v1(generation, changed_modules, public_interface_changed)`, and its driver constructs one global public-interface flag from the environment. Both branches therefore share one classification. A route-level test must provision real admitted archives for retained b and assert returned dirty records plus byte-identical retained artifact. Do not add a new precise API until the driver supplies authoritative per-module changes and migration behavior is designed.
3. **PSI-REQ-004 / persisted corruption.** Publish through the real owner, save CURRENT and generation bytes, corrupt only a generation payload, and read through `package_module_index_read_current_v1`. Require invalid result with the precise digest/admission error and no fallback scan or write. Restore original bytes and require valid read. Separately corrupt CURRENT, use a missing generation, and truncate metadata; retain the previous admitted generation unless an explicit bounded rebuild is authorized. Decode-only tests cannot cover this storage boundary.
4. **PSI-REQ-005 / changed binding.** Publish a valid graph and independently alter expected revision, tree, inventory, producer, root generation, and variant. For each route call, require the exact mismatch reason, no source paths/archive admissions, and unchanged CURRENT bytes. A single combined mismatch is insufficient because it observes only the first check.

## Shared interfaces and manual rules

### Concrete executable additions

| Executable source | Cases | Execution status |
|---|---|---|
| `test/01_unit/compiler/cache/package_module_index_gc_publication_spec.spl` | Publication-lock exclusion, retained generation, post-unlock collection | UNEXECUTED; GC repair exists |
| `test/01_unit/compiler/cache/package_module_index_reader_transaction_spec.spl` | Reader contention, owned snapshot after collection, absent-root compatibility, error-path unlock | UNEXECUTED; reader repair implemented |
| `test/02_integration/compiler/cache/package_index_persistence_admission_spec.spl` | Tampered payload, invalid pointer, empty pointer, absent generation and restoration | UNEXECUTED; uses actual persistence owners |

These eight scenarios do not replace the 44 compiler system scenarios. Owner
corruption/refusal behavior is a prerequisite; production scan counters, compile
sets, archive behavior, crash timing, daemon/remote lifecycle and output parity
still require their own witnesses. Runtime provenance investigation is recorded
in `doc/08_tracking/bug/item6_acceptance_runtime_unavailable_2026-10-03.md`.

Reader acquisition was a separate OPEN case in the original audit. Actual current consumers own
decoded generation values, so the selected repair is atomic pointer/payload
capture, followed by hash/decode outside the lock. Test lock contention refusal,
successful admission after release, and unchanged owned A after publishing B
and collecting A's file. A process-barrier reader/publisher/GC case still needs
execution. The original unlocked pointer/payload sequence was unsafe, and a
caller-supplied retained list is not a lease for lazy-index/archive consumers.
The held-publication-lock test does not certify those separate lifetimes.

Use existing `PackageIndexRouteV1`, `PackageModuleIndexReadV1`, `PackageModuleChangeV1`, `package_index_route_current_v1`, and production publish/read/invalidate owners. Preserve the canonical conceptual record names and PSI IDs in the parent plan. A future `run_package_index_scenario(name)` helper is allowed only when it invokes the real compiler and returns admitted evidence; no synthetic receipt adapter is planned.

Retain existing scenario step labels. New focused labels agreed with the integration owner are `Admit the current package index`, `Reject a changed index binding`, and `Preserve the prior admitted generation`. Use setup/teardown hooks for isolated cache and environment cleanup. Never use sleeps as race synchronization; use a held lock or explicit barrier. Assertions must inspect returned production records and persisted bytes. Placeholder bodies must fail explicitly rather than create green coverage.

## Implementation update after PRs #2299 and #2305

The shell launcher now exists and executes only a separately compiled acceptance
binary. Its Simple entrypoint is `src/app/test/package_index_acceptance.spl`.
Explicit `--scope owner` checks call production persistence, metadata, parser,
snapshot, scheduling, daemon and remote-content owners. Default scope continues
to return incomplete when actual compiler completion, filesystem observations,
process crash injection or performance evidence is missing. Owner scope is not
a replacement for any canonical system assertion above.

The reader captures CURRENT and payload while holding the publication lock.
The production driver now uses admitted previous/current semantic transitions
to derive per-module changes; incompatible/missing transition evidence retains
conservative invalidation. The former global environment flag no longer supplies
semantic authority. These changes supersede the original source-gap descriptions
in the TDD list; all new executable specs remain UNEXECUTED.

Additional focused specs cover mixed private/public edits, omitted change hints,
metadata producer/SMF identity, section arithmetic bounds, actual comment and
whitespace parsing, Git event refresh, frozen-source refusal, snapshot retention,
remote payload forgery and daemon request-token lifetime. See the implementation
design at `doc/05_design/compiler/perf/item6_request_and_remote_admission_2026-10-03.md`.
Full 44-scenario qualification and generated-manual evidence remain outstanding.

Generate manuals from the executable spec with the admitted SPipe docgen after executable tests run. Preserve evidence links, input/runtime digests, scenario status, and requirement traceability; never label this planning appendix as generated execution evidence.

## Acceptance evidence required before completion

- All 44 canonical scenarios run against real production boundaries with source-open/scan counters, fixture and runtime identities, and immutable snapshot/index bindings.
- Focused regressions retain baseline RED and post-fix GREEN evidence. No test may become green solely by printing the expected contract.
- Reproducibility compares actual persisted output/header/archive/plan/receipt bytes or their bound digests across clean/warm and required modes.
- NFR performance records warm startup, representative request latency, maximum RSS, and realistic fixture size; correctness strings alone do not establish performance.
- Existing requirement/design/manual links stay current; generated manuals follow executable steps. A focused GC PASS does not complete Item 6.
- Stop after three repair cycles; never rerun already-green criteria without a relevant change.

## Open production reachability gap: snapshot-derived root generation

Status: **unresolved design/implementation gap**, found by source review on
2026-10-03. This is not a runtime RED/GREEN result. It blocks claiming that the
real cold publisher preserves consumer reuse for a private source edit
(`PSI-REQ-002`, `PSI-NFR-004`). Conservative invalidation remains correct.

The sole production construction of `PackageModuleIndexBuildAuthorityV1` is in
`src/compiler/80.driver/cache/cold_full_index_producer_v1.spl`, in
`cold_full_index_publish_from_driver_v1`. It supplies `snapshot.tree_id` as both
the root-generation seed and the separate SCV tree binding. In
`src/compiler/80.driver/cache/package_module_index_builder.spl`,
`package_module_index_root_for_variant_v1` hashes that seed with the variant.
Therefore a source edit that changes the admitted snapshot tree also changes
the package-index root generation.

The integrated `package_index_route_admitted_invalidation_v1` deliberately
requires equal old/new root generations before accepting precise per-module
semantic changes. A publisher-produced source edit fails this guard and uses
conservative public-change propagation. Tests which retain an invented constant
root generation exercise the classifier but do not prove this production path.

No established stable authenticated project/root-generation authority was found
in the audited cold-publisher, compiler-entrypoint, or SCV snapshot owners.
The daemon's caller-supplied workspace label is a session isolation key;
`cache_project_namespace()` defaults to the common name `simple`; an absolute
checkout path breaks the required checkout-root reproducibility. None is an
approved replacement for the current root-generation authority. Do not remove
the compatibility guard or substitute one of these values to make tests green.

Resolution requires an explicit authority design that distinguishes stable
package graph ownership from mutable snapshot/tree provenance, preserves
cross-workspace isolation and relocation behavior, and specifies migration of
existing index/archive keys. Apply the selected authority consistently in the
publisher, route admission, archive authority, and transition comparison.

The required regression must start with two actual publisher-produced graphs
from frozen snapshots: change one private producer body and one independent
public export, admit the second publication, and route through the actual driver
entrypoint. Assert that only the public branch's reverse dependents are dirty,
the private branch's consumer archive is retained, and all source/index/archive
bindings name the new snapshot. Also reject a different project/root authority
despite matching module names, and compare identities across relocated copies.
This regression must not manually force equal root generations on the graphs.
