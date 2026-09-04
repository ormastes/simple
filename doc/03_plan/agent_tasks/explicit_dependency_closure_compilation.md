# Frozen Package Compilation Agent Task Plan

## Handoff status

Design complete; production implementation not started by this lane. The tasks
below cover all pending implementation. No item is intentionally unassigned.
Agents shall preserve concurrent dirty work and edit only their owned paths.

Primary merge owner and final reviewer: normal/highest-capability Codex session.
Lower-model sidecars may perform read-only audits, but cannot approve interfaces,
exclusions, generated manuals, or done marks. Current agent-spawn interface:
`N/A`; this plan is the concrete handoff for a later implementation launch.

## Frozen shared interfaces

Before parallel edits, A0 publishes exact contracts for:

`ScvBuildSnapshotV1`, `ScvRevisionIdentityV1`, `ScvFileInventoryV1`,
`ScvSnapshotReceiptV1`, `PackageTldrV1`, `PackageSummarySmfV1`,
`PackageSourceSetV1`, `PackageImportEdgeV1`, `PackageRuntimeNeedsV1`,
`PackageCatalogEntryV1`, `PackageCatalogSnapshotV1`,
`PackageActionIdentityV1`, `PackageClosurePlanV1`, `PackageSccV1`,
`PackageCompileResultV1`, and `PackageInvalidationPlanV1`.

Shared SPipe step/helper names are exactly those in
`doc/03_plan/sys_test/explicit_dependency_closure_compilation.md`.

## Parallel lanes

### A0 — Interface and policy freeze

- **Owns:** new model/codec stubs under `src/compiler/00.common/package_metadata/`;
  requirement/design consistency updates only.
- **Delivers:** canonical schemas, error codes, domain-separated digest rules,
  compatibility/version policy, compile-time imports for all lanes.
- **Blocks:** A1–A14 code merge; may be reviewed in parallel.
- **Accept:** canonical round trips and no I/O in common value modules.

### A1 — Non-mutating SCV build freeze

- **Owns:** new `src/lib/scv/build_freeze/{model,inventory,snapshot,lease}.spl`.
- **Delivers:** stable capture, immutable `build/scv/` revision, lease, snapshot
  reads, provenance, no user SCV commit/workspace advancement.
- **Depends:** A0.
- **Accept:** ST-001..003, ST-021 source-isolation subset.

### A2 — SCV events and read-only Git adapter

- **Owns:** new `src/lib/scv/build_freeze/{event_sync,git_readonly}.spl` and only
  required exports; do not modify A1 files.
- **Delivers:** coalesced event generations, `GIT_OPTIONAL_LOCKS=0` allowlist,
  reconciliation receipt, quiet success.
- **Depends:** A0; integrates with A1 interface.
- **Accept:** ST-004..005 and forbidden Git command tests.

### A3 — Snapshot recovery and GC

- **Owns:** new `src/lib/scv/build_freeze/{recover,gc,receipt}.spl`.
- **Delivers:** staging recovery, lease-aware bounded GC, quarantine/receipts.
- **Depends:** A0/A1 contract only.
- **Accept:** ST-020 snapshot boundaries and ST-022.

### A4 — Package metadata codec

- **Owns:** `src/compiler/00.common/package_metadata/{tldr,smf,codec}.spl` after A0
  contract files are frozen.
- **Delivers:** indexed TLDR/SMF encoding, strict decoder, self-seals, section
  lazy access, separate content/semantic digests.
- **Depends:** A0.
- **Accept:** ST-007..008 plus corruption matrix.

### A5 — Catalog storage/admission/publication

- **Owns:** `src/compiler/80.driver/package_catalog/`.
- **Delivers:** SCV/variant namespaces, immutable generations, atomic `CURRENT`,
  recovery, cross-reference validation.
- **Depends:** A0/A1/A4.
- **Accept:** ST-006, catalog half of ST-020.

### A6 — Metadata resolver and explicit closure

- **Owns:** `src/compiler/80.driver/package_graph/{resolver,closure}.spl`.
- **Delivers:** direct catalog lookup, metadata-only BFS, resolver/access receipt,
  undeclared-read failure, bootstrap interface seam.
- **Depends:** A0/A5.
- **Accept:** ST-009 and graph read-count gates.

### A7 — Dirty mapping and semantic invalidation

- **Owns:** `src/compiler/80.driver/package_graph/invalidation.spl` and narrowly
  scoped adapters to existing reverse-reference receipts.
- **Delivers:** snapshot inventory diff, source-set mapping, dimension-specific
  semantic early cutoff, missing-receipt policy.
- **Depends:** A0/A4/A5.
- **Accept:** ST-010..014.

### A8 — SCC condensation

- **Owns:** `src/compiler/80.driver/package_graph/scc.spl`.
- **Delivers:** deterministic Tarjan, canonical SCC/action identity, condensation
  DAG and cycle diagnostics.
- **Depends:** A0/A6.
- **Accept:** ST-016 and permutation determinism tests.

### A9 — Deterministic parallel scheduler

- **Owns:** `src/compiler/80.driver/package_graph/scheduler.spl`.
- **Delivers:** bounded ready queue, owner-result workers, parent-authoritative
  canonical commit, cancellation/failure ordering.
- **Depends:** A0/A8; follow parallel-ownership skill.
- **Accept:** ST-017, once-only action and RSS gates.

### A10 — Package compile action and archive cache

- **Owns:** `src/compiler/80.driver/package_compile/{action,archive}.spl` plus
  narrowly scoped phase adapters; no graph logic.
- **Delivers:** action IDs, package/SCC archive, dependency summary consumption,
  local cache admission.
- **Depends:** A0/A4/A7/A8.
- **Accept:** ST-015 and clean source-open gate.

### A11 — Generated inputs and variants

- **Owns:** `src/compiler/80.driver/package_compile/generated.spl` and
  `src/compiler/80.driver/package_catalog/variant.spl`.
- **Delivers:** declared generator actions/internal outputs, tags/config/provider
  variant identity, no worktree writes.
- **Depends:** A0/A1/A4/A10 contracts.
- **Accept:** ST-018..019.

### A12 — Daemon reuse and remote boundary

- **Owns:** new package-generation cache adapters in watcher/MCP/LSP driver-owned
  modules and `src/compiler/80.driver/package_compile/remote.spl`.
- **Delivers:** generation pinning, decoded-section reuse, immutable remote blob
  readmission, bounded retained state.
- **Depends:** A5/A10.
- **Accept:** ST-023..024 and daemon RSS gate.

### A13 — Bootstrap and cutover

- **Owns:** package-mode adapters in driver source loading, CLI compile entry,
  and bootstrap scripts; only this lane may remove duplicate closure walkers.
- **Delivers:** frozen explicit-root bootstrap, first catalog publication,
  package-mode default, broad-fallback fail gate, staged removal after parity.
- **Depends:** A1/A5/A6/A7/A10.
- **Accept:** ST-025..026 and core/bootstrap smoke matrix.

### A14 — SPipe, diagnostics, evidence, integration review

- **Owns:** planned system spec/manual, package feature unit/integration tests,
  access/Git-state/crash/perf checkers, final traceability report.
- **Delivers:** real SPipe assertions, deterministic diagnostics/access broker,
  benchmark baselines, no-stub scan, combined review of A1–A13.
- **Depends:** shared vocabulary from A0; can scaffold fail-fast tests early and
  complete assertions after implementation.
- **Accept:** all ST/NFR evidence and final `$verify` PASS.

## Integration waves

1. **Wave 0:** A0 contract review and freeze.
2. **Wave 1 parallel:** A1, A2, A3, A4.
3. **Wave 2 parallel:** A5, A6, A7, A8.
4. **Wave 3 parallel:** A9, A10, A11.
5. **Wave 4 parallel:** A12, A13; A14 continuously integrates tests/evidence.
6. **Final:** merge owner resolves interface drift, runs each acceptance gate at
   most once, and requests independent highest-capability review.

## Merge rules

- No lane may add a live-worktree fallback, recursive source scan, duplicate
  catalog, or user Git/SCV mutation.
- Cross-lane changes require owner acknowledgement; do not edit another lane’s
  dirty file to “help.”
- Workers never publish global state; only parent/catalog owner commits results.
- Untracked concurrent `src/lib/scv/compile_snapshot.spl` remains outside this
  plan until its owner reconciles it with REQ-003.
- Production rollout requires executable SPipe evidence, deployed self-hosted
  compiler checks, bootstrap checks, MCP/LSP startup/hot-path/RSS evidence, and
  final verification PASS before any release.
