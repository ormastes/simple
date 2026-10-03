# Item 6 compile optimization: current-source research

Date: 2026-10-03. Inspected base: `7d16ab11d2227cbe5f29dc998b76a1eff326abbb`
(`release/1.0`). Research lane: `work/item6-research-20261003`.
This is additive research; historical findings remain intact. Source inspection
is not native execution evidence, and no completion or performance PASS is claimed.

## Scope and authority

The governing [seven-item plan](../../03_plan/seven_plans_host_completion_2026-09-29.md)
item 6 requires clean/warm/no-op/edit baselines, stage attribution, indexing,
caching, dependency tracking, semantic invalidation, corrupt-cache recovery,
uncached equivalence, and affected bootstrap/runtime/MCP/LSP qualification.
Its persistent-index reference explicitly does not replace the full scope.

Existing user-selected requirements supply retained scope:

- [Semantic cache requirements](../../02_requirements/feature/compiler_semantic_cache_daemon_virtual_summary.md):
  REQ-CSM-001–006 snapshot and action identity; 007–012A storage/lifecycle;
  016–017 AST/summary reuse; 023–025 shadow/parity/admission;
  027 strict three-payload eligibility and explicit fallback.
- [Performance requirements](../../02_requirements/feature/simple_compiler_performance_memory_efficiency.md):
  REQ-006 shared frontend, REQ-019 summary invalidation, REQ-023 compiler hot
  paths, REQ-024 pure-Simple ownership, REQ-025 traceability. The broader
  optimizer transformation program is related retained work, not evidence that
  every optimizer feature belongs exclusively to item 6.
- [Performance NFRs](../../02_requirements/nfr/simple_compiler_performance_memory_efficiency.md):
  NFR-005 memory bound, 006 zero-scan warm tooling, 011 measurement provenance,
  013 startup/request qualification, 015 bounded verification.

No new feature/NFR option is selected by this research. The updated parent plan
must reconcile these authorities rather than rename the index subset “final”.

## Current implementation findings

| Finding | Exact owner at inspected base | Consequence |
|---|---|---|
| Per-module semantic deltas exist | `src/compiler/80.driver/cache/package_module_index.spl`, `PackageModuleChangeV1`, `package_module_index_invalidate_changes_v1` | Export, ABI, initializer and provider deltas propagate; content-only roots stay local. Reuse this owner. |
| Production ordinary route still accepts one batch-wide boolean | `src/compiler/80.driver/cache/package_index_route.spl:109`, `package_index_route_current_v1`; line 192 calls `package_module_index_invalidate_v1` | A mixed private/public batch cannot express which roots changed semantic output. This is a concrete precision gap, not proof of stale output. |
| Driver feeds that coarse flag from facade environment | `src/compiler/80.driver/driver_source_pipeline_loading.spl:331`, `SIMPLE_PACKAGE_INDEX_PUBLIC_INTERFACE_CHANGED` | Precise integration needs admitted per-module change facts, not user-supplied assertions that exports stayed unchanged. Preserve conservative compatibility until provenance is available. |
| Full-inventory cold publication now exists | `src/compiler/80.driver/cache/cold_hir_compiler_publication_v1.spl:291`, `cold_hir_compiler_publish_full_v2`; `cold_full_index_producer_v1.spl:119` | Historical plan statements saying there is no publisher are stale as descriptions of this base. Existence does not prove all production routes are qualified. |
| Bootstrap builder calls the producer | `src/app/bootstrap_builder/native_group_index_build.spl:234` | Trace this actual integration for cold/warm evidence instead of testing only invented fixture publication. |
| Variant receipt is compiler-authored and index-bound | `src/compiler/80.driver/cache/package_config_variant_receipt.spl`, `PackageConfigVariantReceiptV1` | Existing receipt binds producer/index and canonical variant, including target/backend/features/options/environment. Adversarial tests should mutate each dimension independently. |
| Existing system spec depends on an absent script | `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`; missing `scripts/check/check-persistent-smf-package-index.shs` | Exact-base `git show` rejects the script path. Its shell-output assertions cannot currently provide executable production acceptance evidence. |

The route pins SCV revision/tree/inventory and producer/root/variant identities,
rejects mismatches, and reports explicit cold initialization on failed admission.
The closure walker repeatedly calls `package_module_index_find_v1`; invalidation
also uses array membership for accumulated reverse consumers. These are candidate
measurement sites, not established regressions or justification for an unmeasured rewrite.

## Concrete acceptance candidates within retained scope

These are proposed test refinements of existing requirements, not new selected
product options. The parent owns final IDs, helper names and implementation order.

| Case | Setup/change | Required observation | Existing authority |
|---|---|---|---|
| Mixed semantic batch | Two disjoint chains `a -> a_client`, `b -> b_client`; edit a public output and b private body | Exact dirty set `a,a_client,b`; `b_client` admitted unchanged | Index plan invalidation 1,2,7; REQ-019 |
| All semantic dimensions | Independently change export, ABI, initializer, provider | Each propagates only its reverse closure; pure content does not | Existing `PackageModuleChangeV1`; REQ-CSM-005 |
| Same output cutoff | Recompute module after edit, exported semantic fingerprints unchanged | Producer action changes; no downstream compile; output equals fresh build | Index plan 3.7; REQ-019 |
| No-op production compile | Explicitly initialize real fixture, then invoke same admitted binary again | Zero root scans; no dependency source-body reads; stable executable bytes | Index plan acceptance; NFR-006 |
| Identity refusal | Mutate target/compiler/config/generated input independently | Named cache miss/refusal, no stale hit; fresh and cached behavior match | REQ-CSM-005–006 |
| Corrupt generation | Truncate/tamper object or CURRENT after valid publication | No partial read, no hidden scan; explicit recovery publishes a complete generation | REQ-CSM-003,024; index atomic publication |
| Crash/concurrent publication | Interrupt before/after pointer publication with pinned reader | Reader observes one complete generation; previous generation survives failed candidate | REQ-CSM-008,012 |
| Performance cohort | Paired admitted native baseline/candidate; clean, warm, no-op, edit | Source/binary/toolchain/fixture hashes, stage counters, distribution and peak RSS; retained budgets evaluated | NFR-005,011,013 |

Modern SSpec should assert production-returned state and real filesystem/artifact
effects, with named `step(...)` explanations and explicit requirement tags. A unit
test of the delta reducer is necessary for the mixed-batch bug but does not prove
driver cutover, crash recovery or end-to-end performance. Keep those rows OPEN
until their own actual witnesses pass. Never replace the missing script with a
constant-output witness or count a model fixture as a native compiler cohort.

## Evidence and next boundary

This lane inspected exact-base Git blobs, symbol/call-site searches, selected
requirements, and the existing system spec. It did not run the compiler. The
first TDD slice can expose precise mixed-delta routing through existing typed
change records, preserving old callers and fail-closed admission. Broader wiring
must establish the producer of those trusted deltas before claiming precision
for normal CLI requests. Benchmark and fault-injection extensions remain
required full-scope work after the focused slice.
