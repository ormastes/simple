# Java/Go Fast-Compile Parity with Persistent SMF Index

## Scope

Design production-bound SPipe evidence for Java/Go-style fast compilation backed
by persistent SMF package/module metadata, Java-class-like export headers, and
Go-like package archive reuse. Compilation must traverse only the requested
package and its explicit dependency closure. It must never recover by recursively
scanning unrelated source trees.

This plan is test design only. It does not select or implement compiler storage,
scheduling, or CLI behavior.

## Requirement Contract

| Requirement | Testable contract |
|---|---|
| `PSI-REQ-001` | Compile only the requested package and explicit SMF dependency closure; reuse admitted export/header metadata and package archives without opening dependency bodies. |
| `PSI-REQ-002` | Invalidate direct and indirect reverse dependents at package/SCC granularity, including generated-source and config/build-tag variant identities. |
| `PSI-REQ-003` | Schedule independent packages deterministically, reuse admitted state across warm daemon requests, and reproduce clean-build outputs from warm/cached builds. |
| `PSI-REQ-004` | Missing, stale, corrupt, or tampered metadata fails closed unless an explicit bounded-rebuild policy is supplied; publication and recovery are atomic. |
| `PSI-REQ-005` | Every compile/build binds an immutable SCV revision/tree snapshot, canonical inventory, and content digests before package discovery; all reads remain inside that frozen snapshot. |
| `PSI-REQ-006` | SCV snapshot/index integration is implicit on compile invocation and Git/SCV events, quiet on success, observable by receipts, and writes only owned ignored internal metadata. |
| `PSI-REQ-007` | Each daemon request pins one index generation; remote action/archive content is untrusted and passes complete local admission without supplying graph or dirty-state authority. |
| `PSI-NFR-001` | Every successful or refused operation records zero recursive full-tree scans and zero unrelated source reads. |
| `PSI-NFR-002` | Identical inputs produce byte-identical package headers, archives, plans, dispatch order, commit order, outputs, and receipt digests. |
| `PSI-NFR-003` | Concurrent live-worktree edits cannot alter an active build; drift rejects or schedules a new snapshot-bound build, and snapshot lifecycle is atomic and crash recoverable. |
| `PSI-NFR-004` | Content identity is distinct from semantic/export/initializer/provider identity so comment/whitespace edits never invalidate or recompile dependents when compile-relevant metadata is unchanged. |

## Research Coordination

The package-compilation research lane must map its findings to these provisional
shared names rather than inventing a parallel test vocabulary:

- `PersistentSmfPackageIndexV1`: immutable package/module metadata generation.
- `PackageTldrHeaderV1`: bounded closure header and section directory consumed
  without reading dependency source bodies.
- `PackageExportSmfV1`: indexed Java-class-like deep public/export/type,
  initializer, provider, macro/AOP, and generated-input sections.
- `PackageActionKeyV1`: exact package source, dependency, variant, compiler,
  provider, SDK/toolchain, generated-input, and policy identity.
- `PackageArchiveReceiptV1`: Go-like compiled package archive identity and
  admitted cache-hit evidence.
- `ConfigVariantKeyV1`: target, configuration, feature/build-tag, generated
  input, producer, and toolchain identity.
- `PackageCompilePlanV1`: requested root, explicit closure, SCCs, invalidations,
  ready sets, deterministic dispatch order, and producer/toolchain identities.
- `PackageCompileReceiptV1`: actual source-open set, compiled packages, retained
  packages, scan counters, schedule digest, and published index generation.
- `PackageDaemonSessionReceiptV1`: warm index/archive generations, reload count,
  request sequence, and cross-request reuse evidence.
- `ScvCompileSnapshotV1`: immutable SCV `revision_id`, `tree_id`, canonical file
  inventory digest, object/content digests, snapshot root, and lifecycle state.
- `ScvFrozenSourceProviderV1`: the compiler's only source provider after build
  admission; live-worktree access is unavailable rather than a fallback.
- `ScvCompileBridgeReceiptV1`: implicit/explicit mode, triggering Git/SCV event,
  snapshot revision, internal write set, diagnostic status, and package-index
  generation under `build/scv/compile/`.
- `PackageSemanticIdentityV1`: separately framed content, semantic/export,
  initializer, and provider digests used for invalidation decisions.
- `PackageIndexRecoveryPolicyV1`: `deny` or explicitly authorized `bounded`.
- Production checker: `scripts/check/check-persistent-smf-package-index.shs`.

If research changes any shared name, it must update this plan, the executable
spec, and the manual together. Research may refine storage format or algorithms,
but it must preserve every observable contract below.

## Fixture Graph

The future production fixture is rooted at
`test/fixtures/compiler/persistent_smf_package_index/` and contains:

- `app -> api, util`
- `api -> model`
- `util -> model`
- `bundle -> alpha, beta`, where `alpha` and `beta` are independent
- `root -> cycle_a`, with `cycle_a <-> cycle_b`
- `generated_app -> generated_api`, where `generated_api` binds generator input,
  producer executable, and generated output digests
- `variant_app -> variant_lib`, with debug/release configurations and
  `feature_x`/`feature_y` build-tag variants
- `unrelated_secret`, absent from every requested closure and made unreadable
  during the isolation scenario

The checker must invoke the production compiler/index owner. It must not derive
the graph, expected invalidation set, schedule, or index validity itself.

## Checker Contract

Invocation:

```sh
sh scripts/check/check-persistent-smf-package-index.shs --scenario <name>
```

The checker returns zero only after validating compiler-produced
`PackageCompilePlanV1` and `PackageCompileReceiptV1` artifacts. Evidence must bind
the compiler executable digest, fixture digest, index generation, package SMF
digests, and recovery policy. Source-open and recursive-scan counters must come
from the production filesystem/index boundary, not source-string inspection or
test-side reconstruction.

Required scenario names:

1. `explicit-closure-only`
2. `unrelated-tree-unreadable`
3. `header-metadata-reuse`
4. `package-archive-cache-hit`
5. `direct-reverse-invalidation`
6. `indirect-reverse-invalidation`
7. `generated-source-invalidation`
8. `config-variant-isolation`
9. `build-tag-variant-isolation`
10. `deterministic-independent-schedule`
11. `scc-group-invalidation`
12. `daemon-warm-reuse`
13. `clean-warm-reproducibility`
14. `missing-index-denied`
15. `missing-index-bounded-rebuild`
16. `stale-index-denied`
17. `corrupt-metadata-denied`
18. `tampered-index-denied`
19. `crash-before-publish`
20. `crash-after-publish`
21. `no-hidden-full-scan-fallback`
22. `scv-snapshot-bound-build`
23. `scv-concurrent-worktree-edit-isolated`
24. `scv-source-drift-new-build`
25. `scv-snapshot-create-crash`
26. `scv-snapshot-cleanup-crash`
27. `scv-provenance-binding`
28. `scv-no-live-worktree-fallback`
29. `scv-implicit-compile-quiet`
30. `scv-git-event-auto-index-update`
31. `scv-internal-write-boundary`
32. `comment-only-semantic-reuse`
33. `whitespace-only-semantic-reuse`
34. `scv-git-state-nonmutation`
35. `scv-concise-failure-diagnostics`
36. `scv-internal-metadata-atomic-gc`
37. `metadata-section-lazy-read`
38. `private-body-export-early-cutoff`
39. `generated-output-undeclared-denied`
40. `daemon-generation-workspace-isolation`
41. `remote-cache-local-admission`
42. `remote-cache-poison-denied`
43. `cross-mode-reproducibility`
44. `entrypoint-no-scan-matrix`

## SPipe Manual Flow Names

Every scenario uses the same three current manual step labels, in order. Its
scenario-specific setup and assertions remain named in the executable spec:

1. `Prepare the frozen package fixture`
2. `Execute the production compiler scenario`
3. `Verify compiler-bound evidence`

## Acceptance Matrix

The canonical source of names and baseline assertions is the executable spec at
`test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`.
The table below is the full 44-scenario contract. “Gap at base” records what
the `c7f8d22a` source tree actually proves today; a present helper is not proof
that its production path satisfies the acceptance criterion. Every row remains
RED until the checker reports compiler-produced plan/receipt evidence.

| # / scenario | Requirement | Production owner and callable surface | Fixture mutation | Compiler-bound measurement/evidence | Gap at base |
|---|---|---|---|---|---|
| 1 `explicit-closure-only` | REQ-001, NFR-001 | `package_index_route_current_v1`; `driver_source_pipeline_loading` | Request `app` in `model -> api,util -> app` graph | requested root, resolved/opened/compiled exact `model,api,util,app`; scan count | Route exists; no production compile plan/receipt type or admitted checker harness. |
| 2 `unrelated-tree-unreadable` | REQ-001, NFR-001 | source loading owner plus filesystem open/scan boundary | Make `unrelated_secret` inaccessible, compile app | compile success, unrelated opens 0, recursive scans 0 | No source-open/scan receipt boundary or runnable checker. |
| 3 `header-metadata-reuse` | REQ-001 | `package_tldr_admit_v1`; `package_archive_load_v1`; driver lowering | Poison/deny dependency source bodies after fixture admission | TLDR header cache hits; source body opens 0; export ABI digest matches | Admission helpers exist; end-to-end header-only load and counters unproved. |
| 4 `metadata-section-lazy-read` | REQ-001 | `package_export_smf_section_v1`; `package_tldr_admit_v1` | Add unreached section and request one demanded section | reached headers list, demanded sections only, unreached reads 0 | Section helpers exist; production read instrumentation and demand path unproved. |
| 5 `package-archive-cache-hit` | REQ-001, NFR-002 | `package_archive_load_v1`; `package_archive_receipt_decode_v1` | Seed admitted model/api/util archive receipts and repeat compile | archive hits; dependency recompile count 0; variant/action/member digests match | Archive API exists; production compile receipt and actual cache-hit path unproved. |
| 6 `missing-index-denied` | REQ-004 | `package_module_index_read_current_v1`; `package_index_route_current_v1` | Remove CURRENT/index generation | `PKG-IDX-001`, compile not started, fallback/scan count 0 | Read/admission path exists; compiler error and counters not bound to receipt. |
| 7 `direct-reverse-invalidation` | REQ-002 | `package_module_index_invalidate_v1`; route invalidation | Change util's public export | invalidated/compiled util,app; model,api retained | Invalidation helper exists; fixture-to-compiler mutation and measured compile set unproved. |
| 8 `indirect-reverse-invalidation` | REQ-002 | `package_module_index_invalidate_v1`; `package_scc_schedule_v1` | Change model's public export | model,api,util,app invalidated/compiled; unrelated opens 0 | Same gap: no production scenario harness or emitted evidence. |
| 9 `generated-source-invalidation` | REQ-002, REQ-005 | cold HIR producer/output owners; index builder entry projection | Change generator input and regenerate generated_api | producer/input/output digests; generated_api+generated_app invalidation; unchanged archive reuse | Concrete gap: generated digest reaches TLDR but builder entry drops it; index entry/route transition lack generated field/comparison. Also no real scenario runner. |
| 10 `config-variant-isolation` | REQ-002 | `config_variant_encode_v1`, `config_variant_digest_v1`; package config receipt owner | Change debug variant only | debug invalidated; release retained; no cross-variant reuse | Variant identity helpers exist; compile/archive binding evidence unproved. |
| 11 `build-tag-variant-isolation` | REQ-002 | config variant key/digest and package-index route | Switch feature_x while retaining feature_y | ConfigVariantKeyV1 match; affected tag only; cross-variant hits 0 | Key helpers exist; source/tag derivation and end-to-end isolation unproved. |
| 12 `private-body-export-early-cutoff` | REQ-002, NFR-004 | `package_tldr_early_cutoff_v1`; semantic transition owner | Change private body without export change | producer archive changes; export digest stable; propagation stops; consumers compile 0 | Early-cutoff helper exists; semantic field ownership/effect on production reverse graph unproved. |
| 13 `generated-output-undeclared-denied` | REQ-002, REQ-004 | index builder and cold generated-output owner | Add undeclared output or omit producer binding | `PKG-IDX-004`; generated output rejected; index/cache publish 0 | Generated identity field is omitted in builder projection; no production checker proving deny-before-publish. |
| 14 `deterministic-independent-schedule` | REQ-003, NFR-002 | `package_scc_schedule_v1`; compile dispatch/commit owner | Repeat bundle build with alpha/beta ready together | ready, dispatch, commit order and schedule digest match | Scheduler helper exists; dispatch implementation and repeatable production receipt unproved. |
| 15 `scc-group-invalidation` | REQ-003 | `package_scc_schedule_v1`; `package_scc_consume_index_schedule_v1` | Change cycle_a in cycle_a <-> cycle_b -> root | SCC invalidation cycle_a,cycle_b; reverse root; compile set exact | SCC helpers exist; production graph and receipt evidence unproved. |
| 16 `daemon-warm-reuse` | REQ-003 | `PackageDaemonSessionV1`; package route/archive owners | Submit same request twice in one daemon | session receipt; index reload 0; second compile 0; archive hits | Session model exists; session integration in actual daemon request path and receipt absent. |
| 17 `clean-warm-reproducibility` | REQ-003, NFR-002 | index/archive owners and plan/receipt producer | Compare clean build with warm cache build | output/header/archive/plan/receipt digests equal | `PackageCompilePlanV1`/`PackageCompileReceiptV1` production definitions and evidence producer absent. |
| 18 `missing-index-bounded-rebuild` | REQ-004 | builder `package_module_index_build_from_inventory_v1`; atomic publisher | Remove index; authorize declared finite roots | roots read exactly once; scans 0; atomic publication | Builder/publisher exist; policy authority and bounded rebuild CLI integration unproved. |
| 19 `stale-index-denied` | REQ-004 | `package_index_route_current_v1`; index admission | Change source inventory after index generation | `PKG-IDX-002`; compile not started; prior generation preserved; scans 0 | Admission compares authority fields; real stale fixture and compiler evidence unproved. |
| 20 `tampered-index-denied` | REQ-004 | `package_module_index_decode_v1`; `package_module_index_validate_v1` | Alter serialized entry/digest | `PKG-IDX-004`; compile not started; scans 0 | Decode/validation helpers exist; production-bound mutation/diagnostic receipt unproved. |
| 21 `corrupt-metadata-denied` | REQ-004 | `package_tldr_admit_v1`; `package_archive_load_v1` | Corrupt header/SMF before archive open | `PKG-IDX-003`; header/archive consumed false; scans 0 | Local validators exist; consumption boundary evidence unproved. |
| 22 `crash-before-publish` | REQ-004 | `_package_module_index_publish_locked_v1`; archive batch publisher | Inject stop before CURRENT swap | previous generation remains; mixed generation false; temp residue 0 | Atomic publication code exists; fault injection and recovery test absent. |
| 23 `crash-after-publish` | REQ-004 | same index/archive publishers | Interrupt after pointer publication | new complete generation only; mixed false; residue 0 | Same: publication helper is not crash evidence. |
| 24 `no-hidden-full-scan-fallback` | REQ-001, REQ-004, NFR-001 | route failure handling; `driver_source_pipeline_loading` | Deny/corrupt indexed route then observe all reads | production receipt says fallback, recursive scan, unrelated read all 0 | Fail-closed route branches exist; no production boundary counters/compile receipt. |
| 25 `scv-snapshot-bound-build` | REQ-005 | `scv_compile_snapshot_acquire_v1/open_v1`; driver HIR snapshot admission | Start clean snapshot before discovery | canonical inventory finalized; action IDs after; frozen provider identity | SCV snapshot API exists; no `ScvFrozenSourceProviderV1` production integration/plan receipt. |
| 26 `scv-concurrent-worktree-edit-isolated` | REQ-005, NFR-003 | snapshot source owner and compiler source-loading boundary | Edit live file after snapshot admission | active snapshot/plan unchanged; output matches frozen bytes; live reads 0 | Snapshot materialization exists; compiler-wide source-open ownership is not proven. |
| 27 `scv-source-drift-new-build` | REQ-005, NFR-003 | snapshot admission/provenance plus CLI build admission | Change source after frozen inventory; issue next request | drift detected; active build unchanged; distinct revision/build ID or explicit reject | No automatic request bridge/receipt for drift policy. |
| 28 `scv-snapshot-create-crash` | REQ-005, NFR-003 | `scv_compile_snapshot_acquire_v1` staged publisher | Stop during staging before admission | partial snapshot denied; previous intact; orphan staging recovered | Atomic helpers exist; crash hook and lifecycle receipt absent. |
| 29 `scv-snapshot-cleanup-crash` | REQ-005, NFR-003 | SCV snapshot lease/cleanup owner | Stop GC while active and orphan snapshots coexist | active snapshot survives; cleanup idempotent; generation consistent | Snapshot lease/GC production owner and crash evidence not established. |
| 30 `scv-provenance-binding` | REQ-005 | snapshot identity; index builder/route; archive authority | Compile from one revision/tree/inventory | revision/tree/inventory binds plan, action, index, archive and receipt | Some index/archive types carry SCV IDs; full action/plan/receipt chain lacks integrated evidence. |
| 31 `scv-no-live-worktree-fallback` | REQ-005 | driver source owner and snapshot open/admission | Remove/tamper frozen source while live source remains readable | `SCV-BUILD-004`; compile not started; live read/fallback 0 | Driver still has path-based raw source reads; no exclusive source-provider enforcement receipt. |
| 32 `scv-implicit-compile-quiet` | REQ-006 | compile CLI/build admission bridge; snapshot acquire | Invoke ordinary compile without SCV option | automatic snapshot admitted; zero normal output; durable bridge receipt | Existing pipeline consumes SCV environment authority; implicit bridge/receipt type not present. |
| 33 `scv-git-event-auto-index-update` | REQ-006 | Git/SCV event bridge; index builder/publisher | Apply one source event and inspect next generation | affected metadata only; unchanged entries not rewritten; atomic generation | No production event bridge found in compiler owners. |
| 34 `scv-internal-write-boundary` | REQ-006 | compile-cache root/SCV publisher | Trigger automatic snapshot/index write | root exactly ignored `build/scv/compile`; outside/user/developer writes 0 | Existing snapshot cache path is not proof of enforced write-set boundary; no receipt. |
| 35 `comment-only-semantic-reuse` | REQ-006, NFR-004 | `package_tldr_early_cutoff_v1`; package semantic transition owner | Comment-only edit to frozen dependency | raw content differs; semantic/export/initializer/provider stable; dependent invalidation/recompile 0 | Early cutoff surface exists; no complete semantic identity/compiled path evidence. |
| 36 `whitespace-only-semantic-reuse` | REQ-006, NFR-004 | same semantic transition and invalidation owners | Whitespace-only edit to frozen dependency | same digest/count evidence as comment-only | Same gap; production receipt absent. |
| 37 `scv-git-state-nonmutation` | REQ-006 | SCV bridge and internal write owner | Snapshot and compile; compare Git index, refs, HEAD, locks | state digests equal; Git mutation command count 0 | No automatic bridge run; no owned Git-state evidence source. |
| 38 `scv-concise-failure-diagnostics` | REQ-006 | compile CLI diagnostics/receipt owner | Run quiet success and one denied/drift case | success lines 0; failure stable code, bounded text and receipt path | No bridge receipt/diagnostic owner implemented as a joined path. |
| 39 `scv-internal-metadata-atomic-gc` | REQ-006 | SCV compile metadata publisher/GC | Publish then collect expired generation; interrupt publication | bounded size, owner marker, GC receipt, no partial CURRENT | Snapshot primitives exist; compile metadata root/GC receipt contract unproved. |
| 40 `daemon-generation-workspace-isolation` | REQ-007 | `PackageDaemonSessionV1`; actual daemon workspace/request owner | Refresh index during request, between requests, close workspace | one generation/request; between-request refresh; zero remaining pins/dirty state | Session type exists; daemon routing/teardown integration and counters absent. |
| 41 `remote-cache-local-admission` | REQ-007 | archive/action admission owners plus remote cache adapter | Supply remote bytes with untrusted graph/policy metadata | local action/member admission complete; remote graph/dirty/generation authority false | No production remote adapter path/evidence found in package cache owner. |
| 42 `remote-cache-poison-denied` | REQ-007 | same remote adapter and archive validators | Poison cross-variant/workspace or payload mismatch | `PKG-IDX-005`; reject before graph mutation; scans/fallback 0 | Remote admission path absent; validator helpers alone do not establish poisoning defense. |
| 43 `cross-mode-reproducibility` | REQ-003, REQ-007, NFR-002 | plan/receipt producer across driver/daemon/cache paths | Vary workers, daemon restart, cwd/root, local vs remote | normalized semantic evidence digests all equal | Plan/receipt evidence producer and remote path absent; no matrix runner. |
| 44 `entrypoint-no-scan-matrix` | REQ-001, REQ-004, NFR-001 | compile/check/bootstrap/MCP/LSP/daemon entrypoints + filesystem boundary | Run identical isolated fixture through every entrypoint | entrypoint list exact; scan/unrelated reads/discovery subprocesses all 0 | No cross-entrypoint boundary instrumentation or compiled acceptance runner. |

## Fail-Fast Rules

- A missing production checker, receipt, index digest, source-open trace, or scan
  counter is a failing test, never a skip or structural PASS.
- The checker may not create expected receipts or precompute the expected graph.
- No source grep, fixture inventory, or mocked scheduler can satisfy runtime
  package-compilation evidence.
- A bounded rebuild must have explicit `PackageIndexRecoveryPolicyV1` authority
  and a declared finite root set; an unrestricted workspace walk is forbidden.
- No scenario may pass from `pass_todo`, tautological assertions, or an empty
  helper body.
- Snapshot inventory must be canonical and complete before discovery: normalized
  repository-relative path, file kind/mode, size, and raw-byte content digest in
  deterministic order. Mtime or live path identity is not admissible.
- The checker must prove that `ScvFrozenSourceProviderV1` owns every source read;
  merely comparing pre/post worktree hashes is insufficient.
- A worktree edit may enqueue a new build, but it must never rewrite the active
  snapshot, package index generation, action ID, or compile receipt.
- Automatic mode is mandatory for normal compile/build invocation and source
  events; absence of an explicit SCV flag cannot disable snapshot admission.
- Automatic writes are restricted to ignored `build/scv/compile/` paths. They
  must not touch source, documentation, manifests, project configuration,
  user-authored files, Git index/refs/commits/locks, or developer-file mtimes.
- No automatic path may execute commit, push, index rewrite, ref update, lock
  removal, rebase, reset, checkout, or other history mutation.
- Content digest and `PackageSemanticIdentityV1` fields are independently framed
  and stored. Equal semantic/export/initializer/provider digests forbid reverse-
  dependent invalidation even when frozen raw content changed.
- A remote fixture may provide content bytes only. It may not provide graph
  edges, dirty truth, current-generation authority, policy, or an admission
  verdict, and local validation must cover every archive member payload.
- Generated-source evidence must come from the production generator/action
  owner; test-side metadata or prewritten success receipts are forbidden.

## Missing Implementation Gate Handoff

The implementation lane must close these gates before SPipe can pass. Each gate
must be implemented in production code; the checker may only validate it.

| Gate | Required production capability | Evidence owner |
|---|---|---|
| `PSI-IMP-001` | Persistent `PersistentSmfPackageIndexV1` load/admission/publication with no recursive fallback. | Compiler package-index owner |
| `PSI-IMP-002` | `PackageTldrHeaderV1` plus lazy `PackageExportSmfV1` reuse without dependency source-body reads. | Frontend/HIR metadata owner |
| `PSI-IMP-003` | `PackageActionKeyV1` and `PackageArchiveReceiptV1` lookup with exact input, ordered member-payload, toolchain, target, and variant admission. | Build/cache owner |
| `PSI-IMP-004` | Direct, transitive reverse-reference, and SCC invalidation at package granularity. | Reverse-reference owner |
| `PSI-IMP-005` | Generated-source producer/input/output identity and config/build-tag `ConfigVariantKeyV1`. | Build-input identity owner |
| `PSI-IMP-006` | Deterministic parallel ready-set dispatch plus parent-authoritative commit. | Compile scheduler owner |
| `PSI-IMP-007` | Daemon generation reuse and bounded invalidation across sequential requests. | Compiler daemon owner |
| `PSI-IMP-008` | Production filesystem-boundary open/scan counters proving unrelated directories are never read. | Filesystem/index boundary owner |
| `PSI-IMP-009` | Atomic index/header/archive publication and crash recovery. | Cache publication owner |
| `PSI-IMP-010` | Production-bound fixture/checker and durable receipts for all 44 scenarios. | SPipe implementation owner |
| `PSI-IMP-011` | Atomic `ScvCompileSnapshotV1` creation from SCV revision/tree objects with canonical inventory and digest admission before discovery. | SCV working-copy/store owner |
| `PSI-IMP-012` | `ScvFrozenSourceProviderV1` compiler integration with no live-worktree read API or fallback after admission. | Compiler source-provider owner |
| `PSI-IMP-013` | SCV revision/tree/inventory binding in package index generations, action IDs, headers, archives, outputs, and receipts. | Build identity/provenance owner |
| `PSI-IMP-014` | Snapshot lease, atomic cleanup, orphan recovery, and crash-safe lifecycle receipts. | SCV maintenance/lifecycle owner |
| `PSI-IMP-015` | Transparent compile/Git-event bridge that creates or admits SCV snapshots and updates package metadata without an explicit user option. | CLI/build + SCV event owner |
| `PSI-IMP-016` | Enforced ignored write root `build/scv/compile/`, atomic bounded metadata writes, ownership labels, and GC receipts. | SCV compile-cache owner |
| `PSI-IMP-017` | Separately framed content versus semantic/export/initializer/provider digests and reverse-invalidation suppression. | Frontend identity + reverse-reference owner |
| `PSI-IMP-018` | Quiet-success observability plus concise failure/drift diagnostics with durable `ScvCompileBridgeReceiptV1`. | CLI diagnostics/provenance owner |
| `PSI-IMP-019` | Lazy TLDR/SMF section reader with production source/metadata access counters. | Package metadata owner |
| `PSI-IMP-020` | Byte-identical export early cutoff after private-body recompilation. | Reverse-reference/cache owner |
| `PSI-IMP-021` | Per-request daemon generation pin, between-request refresh, and workspace-state teardown. | Compiler daemon owner |
| `PSI-IMP-022` | Locally verified remote action/archive cache with poisoning and variant/workspace isolation. | Build/cache owner |
| `PSI-IMP-023` | Cross-mode reproducibility normalizer and compile/check/bootstrap/MCP/LSP/daemon no-scan instrumentation. | Driver/filesystem boundary owner |

## Artifacts

- Executable: `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`
- Manual: `doc/06_spec/03_system/compiler/package_index/persistent_smf_package_index_spec.md`

## Current Status

`DESIGNED / EXPECTED RED`: the production checker and persistent package-index
implementation are not claimed by this test-design artifact.
