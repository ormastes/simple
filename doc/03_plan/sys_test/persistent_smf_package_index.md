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

Use these exact manual step labels across the executable and generated manual:

- `Compile the requested package from the persistent SMF index`
- `Reuse dependency export headers without opening source bodies`
- `Reuse admitted package archives`
- `Make the unrelated source tree unreadable`
- `Edit one indexed package`
- `Change a generated source input`
- `Change one configuration or build-tag variant`
- `Schedule independent ready packages`
- `Invalidate one member of a package cycle`
- `Compile a second request in the warm daemon`
- `Compare clean and warm build receipts`
- `Refuse an untrusted package index`
- `Authorize one bounded index rebuild`
- `Interrupt atomic index publication`
- `Inspect the production compile receipt`
- `Freeze one SCV revision before package discovery`
- `Edit the live worktree during the frozen build`
- `Detect source drift without mutating the active build`
- `Interrupt SCV snapshot creation or cleanup`
- `Inspect SCV-bound build provenance`
- `Read only TLDR and demanded SMF sections`
- `Stop invalidation after an unchanged export`
- `Pin and refresh one daemon generation`
- `Admit untrusted remote content locally`
- `Compare reproducible compile modes`
- `Inspect every production entrypoint`
- `Invoke compile without an explicit SCV option`
- `Apply one Git or SCV source event`
- `Inspect automatic SCV internal writes`
- `Edit only comments or whitespace in frozen source`
- `Compare Git state before and after automatic SCV`
- `Inspect quiet success and concise failure diagnostics`

## Acceptance Matrix

| Scenario | Required evidence |
|---|---|
| Explicit closure | Opened and compiled set is exactly `model,api,util,app`; scan count is zero. |
| Unreadable unrelated tree | Compile succeeds; unrelated read count and recursive scan count are zero. |
| Missing index denied | `PKG-IDX-001`; compilation does not start; no fallback scan. |
| Header metadata reuse | Dependency closure metadata is admitted from `PackageTldrHeaderV1` and demanded `PackageExportSmfV1` sections; dependency source-body reads are zero. |
| Package archive hit | Dependency archives are admitted by content/toolchain/variant digest; dependency recompiles are zero. |
| Direct package edit | Editing `util` invalidates/compiles exactly `util,app`; `model,api` remain admitted. |
| Indirect package edit | Editing `model` invalidates/compiles exactly `model,api,util,app`. |
| Generated source | A changed generator input invalidates generated output and reverse dependents; unchanged generated identity stays cached. |
| Config variant | Changing debug/release identity invalidates only the selected variant; other variant archives remain admitted. |
| Build-tag variant | Changing `feature_x`/`feature_y` invalidates only the selected tag closure; no cross-variant archive reuse occurs. |
| Independent schedule | Ready, dispatch, and commit orders are deterministic across repeated runs. |
| SCC invalidation | Editing `cycle_a` invalidates the complete `cycle_a,cycle_b` SCC and reverse dependent `root`. |
| Warm daemon | A second identical request reuses the same admitted index/header/archive generations with no metadata reload or compile. |
| Reproducibility | Clean and warm/cached builds produce byte-identical outputs, headers, archives, plans, and receipts after volatile-field normalization. |
| Authorized rebuild | Bounded policy reads declared manifest roots only, performs no recursive scan, and publishes atomically. |
| Stale index | `PKG-IDX-002`; compilation does not start. |
| Corrupt metadata | `PKG-IDX-003`; compilation does not start and no archive/header is consumed. |
| Tampered index | `PKG-IDX-004`; compilation does not start. |
| Crash before publish | Previous generation remains current; temporary residue is removed. |
| Crash after publish | New complete generation is admitted; no mixed generation is observable. |
| No hidden fallback | Missing/corrupt metadata never triggers a recursive source-tree walk. |
| SCV snapshot admission | Revision, tree, canonical inventory, and file digests finalize before package discovery or action-ID creation. |
| Frozen-source reads | Every source-open receipt resolves beneath `ScvCompileSnapshotV1`; live-worktree read count is zero. |
| Concurrent edit isolation | Editing the live worktree after build admission does not change the active plan, inputs, output, or receipt. |
| Drift handling | Drift either returns `SCV-BUILD-002` or schedules a distinct new snapshot/revision/build ID; the active build remains unchanged. |
| Snapshot creation crash | No partial snapshot becomes admissible; previous admitted snapshot remains intact and orphan staging is recoverable. |
| Snapshot cleanup crash | Active/leased snapshots are never removed; orphan cleanup is idempotent and cannot expose a mixed generation. |
| Provenance | Package index, action IDs, headers, archives, outputs, and receipts bind the same SCV revision/tree/inventory digest. |
| No live fallback | Missing/tampered snapshot data returns `SCV-BUILD-001`/`SCV-BUILD-003`/`SCV-BUILD-004`; live worktree is never consulted. |
| Implicit quiet compile | A normal compile with no SCV option creates/reads the frozen snapshot automatically, emits no success chatter, and retains an observable receipt/log. |
| Git/SCV event update | A source event atomically updates only the affected internal package metadata/index generation before the next build. |
| Internal write boundary | Automatic SCV writes only beneath ignored `build/scv/compile/`; source, docs, manifests, project config, and developer-needed timestamps are unchanged. |
| Git non-mutation | Git index, refs, commits, locks, and history are byte/state identical; no commit, push, rewrite, lock removal, or history command occurs. |
| Comment-only edit | Frozen content digest changes; semantic/export/initializer/provider digests remain stable; changed package may reparse at most once; dependent invalidation/recompile counts are zero. |
| Whitespace-only edit | Same contract as comment-only, including zero dependent invalidation and recompile. |
| Quiet diagnostics | Success uses receipts/logs without normal output; failure/drift emits a stable code and concise bounded diagnostic pointing to evidence. |
| Internal metadata lifecycle | Writes are atomic, bounded, owner-labeled, garbage-collectable, and crash recovery leaves no partial current generation. |
| Lazy metadata sections | Closure planning reads only reached TLDR headers; semantic loading reads only demanded SMF sections and opens zero dependency sources. |
| Private-body early cutoff | The producer action/archive may change, but byte-identical exports stop reverse propagation and retain every consumer. |
| Undeclared generated output | Missing, extra, or unbound generator output returns `PKG-IDX-004`; no index/cache publication occurs. |
| Daemon isolation | One request observes one generation, refresh occurs only between requests, and workspace close releases all pins and dirty state. |
| Remote admission | Remote bytes pass complete local action/archive/member admission; remote graph, dirty-state, generation, and policy authority remain false. |
| Remote poisoning | Cross-workspace, cross-variant, partial, replayed, or payload-mismatched content returns `PKG-IDX-005` without graph mutation or scan fallback. |
| Cross-mode reproducibility | Worker counts, clean/incremental, daemon restart, checkout root/cwd, and local/remote hits produce byte-identical semantic evidence. |
| Entrypoint no-scan matrix | Compile, check, bootstrap, MCP, LSP, daemon startup, and daemon request report zero recursive scans, unrelated reads, and discovery subprocesses. |

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
