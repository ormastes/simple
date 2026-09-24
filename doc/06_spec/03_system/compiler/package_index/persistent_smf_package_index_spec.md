# Java/Go Fast-Compile Parity with Persistent SMF Index

- Executable: `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`
- Test plan: `doc/03_plan/sys_test/persistent_smf_package_index.md`
- Requirements: `PSI-REQ-001`, `PSI-REQ-002`, `PSI-REQ-003`, `PSI-REQ-004`,
  `PSI-REQ-005`, `PSI-REQ-006`, `PSI-REQ-007`, `PSI-NFR-001`, `PSI-NFR-002`, `PSI-NFR-003`,
  `PSI-NFR-004`
- Evidence class: production compiler/index runtime receipt
- Current status: `DESIGNED / EXPECTED RED`

## Purpose

Prove that persistent SMF package metadata supports Java/Go fast-compile parity:
Java-class-like export header reuse, Go-like package archive cache hits, explicit
dependency closure, package/SCC/variant invalidation, deterministic parallel
scheduling, warm daemon reuse, reproducibility, and no unrelated recursive scan.
Every build additionally executes against one immutable SCV revision/tree
snapshot so concurrent live-worktree edits cannot affect active compilation.
SCV admission is automatic and quiet for ordinary compile calls and source
events; it never grants permission to mutate Git or user-authored files.

## Scenario Flow

### Compile only the explicit closure

1. Compile the requested package from the persistent SMF index.
2. Inspect the production compile receipt.
3. Confirm the resolved, opened, and compiled set is exactly
   `model,api,util,app`.
4. Confirm recursive scans are zero.

### Keep unrelated trees unread

1. Make the unrelated source tree unreadable.
2. Compile `app` through the production owner.
3. Confirm compilation succeeds with zero unrelated reads and zero recursive
   scans.

### Reuse export headers and package archives

1. Reuse dependency export headers without opening source bodies.
2. Confirm bounded `PackageTldrHeaderV1` records locate only demanded indexed
   `PackageExportSmfV1` sections.
3. Reuse admitted package actions/archives and confirm input, ordered member
   payload, producer, target, toolchain, and variant identities match.
4. Confirm dependency source-body reads and dependency recompiles are zero.

### Invalidate one package at a time

1. Edit one indexed package (`util`).
2. Compile the requested root again.
3. Confirm only `util` and reverse dependent `app` are invalidated and compiled.
4. Confirm `model` and `api` remain admitted.

### Invalidate indirect and generated dependencies

1. Edit `model` and confirm transitive invalidation of `api`, `util`, and `app`.
2. Change a generated source input.
3. Confirm generator input, producer, and output digests invalidate only
   `generated_api` and `generated_app`.
4. Confirm unchanged generated identities continue to reuse their archive.

### Isolate configuration and build-tag variants

1. Change the debug configuration and retain the release archive.
2. Change `feature_x` and retain the `feature_y` closure.
3. Confirm `ConfigVariantKeyV1` prevents cross-variant archive reuse.

### Schedule independent packages deterministically

1. Schedule independent ready packages `alpha` and `beta`.
2. Confirm deterministic dispatch order `alpha,beta` and commit order
   `alpha,beta,bundle`.
3. Repeat with identical inputs and confirm the schedule digest is identical.

### Invalidate a complete SCC

1. Invalidate one member of the `cycle_a,cycle_b` package cycle.
2. Confirm the complete SCC and reverse dependent `root` are invalidated.
3. Confirm no unrelated package is compiled.

### Reuse a warm daemon and reproduce clean builds

1. Compile a second identical request in the same daemon session.
2. Confirm no index reload or package compilation occurs and all admitted
   package archives are reused.
3. Compare clean and warm builds.
4. Confirm output, export header, archive, plan, and receipt digests match.

### Refuse missing, stale, or tampered indexes

1. Refuse untrusted package metadata without recovery authority.
2. Confirm missing, stale, corrupt, and tampered forms produce `PKG-IDX-001`,
   `PKG-IDX-002`, `PKG-IDX-003`, and `PKG-IDX-004` respectively.
3. Confirm compilation does not start and no fallback scan occurs.

### Allow only a bounded rebuild

1. Authorize one bounded index rebuild.
2. Confirm the production owner reads only declared manifest roots.
3. Confirm recursive scans remain zero and the new index generation publishes
   atomically.

### Recover atomically from interruption

1. Interrupt atomic index publication before publish.
2. Confirm the prior complete generation remains current and temporary residue
   is removed.
3. Interrupt after publish.
4. Confirm only the complete new generation is admitted and no mixed generation
   is observable.

### Prove there is no hidden full-scan fallback

1. Inspect the production compile receipt after refused metadata admission.
2. Confirm fallback scans, recursive scans, and unrelated reads are all zero.
3. Confirm counters originate from the production filesystem/index boundary.

### Freeze SCV before discovery

1. Freeze one SCV revision before package discovery.
2. Confirm the canonical inventory binds normalized path, kind/mode, size, and
   raw-byte digest in deterministic order.
3. Confirm inventory publication completes before package discovery or action-ID
   creation.
4. Confirm all compiler reads use `ScvFrozenSourceProviderV1`.

### Isolate concurrent worktree edits

1. Start a build against an admitted `ScvCompileSnapshotV1`.
2. Edit the corresponding live-worktree source while compilation is active.
3. Confirm the active snapshot, plan, action IDs, inputs, output, and receipt are
   unchanged and match the frozen source.
4. Confirm live-worktree read count is zero.

### Reject drift or schedule a new build

1. Detect source drift after active-build admission.
2. Confirm the active build is never mutated.
3. Confirm policy either rejects with `SCV-BUILD-002` or schedules a distinct
   SCV revision/snapshot and build ID.

### Recover SCV snapshot lifecycle atomically

1. Interrupt snapshot creation before publication.
2. Confirm no partial snapshot is admitted, the prior snapshot remains intact,
   and orphan staging is recoverable.
3. Interrupt cleanup while an active snapshot is leased.
4. Confirm active snapshots are retained, orphan cleanup is idempotent, and no
   mixed snapshot generation appears.

### Bind complete SCV provenance

1. Inspect SCV-bound build provenance.
2. Confirm package index generations, action IDs, export headers, archives,
   outputs, and compile receipts all bind the same `revision_id`, `tree_id`, and
   canonical inventory digest.
3. Remove or tamper with snapshot data and confirm the build fails closed without
   a live-worktree fallback.

### Run automatic SCV quietly

1. Invoke compile without an explicit SCV option.
2. Confirm an immutable snapshot is admitted automatically.
3. Confirm normal success emits no diagnostic chatter while a durable
   `ScvCompileBridgeReceiptV1` remains observable.
4. Apply one Git/SCV source event and confirm only affected internal package
   metadata is atomically advanced.

### Enforce the internal write boundary

1. Inspect every write made by automatic SCV.
2. Confirm all writes stay beneath ignored `build/scv/compile/` and are bounded,
   atomic, owner-labeled, and garbage-collectable.
3. Confirm source, docs, manifests, project config, user-authored files, and
   developer-needed timestamps are unchanged.
4. Confirm Git index, refs, commits, HEAD, locks, and history are unchanged and
   no history mutation command executed.

### Preserve dependents after non-semantic edits

1. Edit only comments in frozen source, then repeat with whitespace only.
2. Confirm raw content digest changes independently from semantic/export,
   initializer, and provider digests.
3. Permit at most one changed-package reparse.
4. Confirm dependent invalidation and dependent recompilation counts remain zero.

### Keep diagnostics quiet and actionable

1. Confirm successful automatic operation emits zero normal diagnostic lines.
2. Trigger failure/drift and confirm a concise bounded diagnostic contains a
   stable code and receipt path.

### Enforce daemon and remote-cache trust boundaries

1. Pin one catalog generation for an entire daemon request and publish a newer
   generation concurrently.
2. Confirm refresh occurs only between requests and workspace close releases
   every generation pin and dirty-state record.
3. Fetch package action/archive bytes from an untrusted remote cache.
4. Confirm complete local admission succeeds for valid bytes and rejects
   poisoned, cross-workspace, cross-variant, partial, or replayed content without
   graph mutation or scan fallback.

### Prove lazy metadata and private-body early cutoff

1. Read only reached TLDR headers and demanded SMF sections for a clean closure.
2. Confirm dependency source opens and unreached metadata reads remain zero.
3. Recompile one private-body edit whose public export metadata is byte-identical.
4. Confirm reverse propagation stops and every consumer remains admitted.
5. Present an undeclared generated output and confirm `PKG-IDX-004` with no
   package-index or cache publication.

### Compare all reproducibility and no-scan modes

1. Compare worker counts, clean/incremental builds, daemon restart, checkout
   roots/cwd, and local/remote cache hits.
2. Confirm byte-identical metadata, plans, archives, diagnostics, receipts, and
   final outputs after normalization.
3. Invoke compile, check, bootstrap, MCP, LSP, daemon startup, and daemon request.
4. Confirm every path reports zero recursive scans, unrelated reads, and
   discovery subprocesses.

## Required Durable Evidence

- `PersistentSmfPackageIndexV1` generation digest
- `PackageTldrHeaderV1` closure/section-directory digest and read count
- demanded `PackageExportSmfV1` section digests and source-body read count
- `PackageActionKeyV1` exact declared-input identity
- `PackageArchiveReceiptV1` ordered member-payload/toolchain/target/variant
  digest and hit count
- `ConfigVariantKeyV1` configuration/build-tag/generated-input identity
- `PackageCompilePlanV1` digest
- `PackageCompileReceiptV1` digest
- `PackageDaemonSessionReceiptV1` generation/reload/request evidence
- local/remote cache source, local admission, rejection, and graph-mutation
  evidence
- compiler executable and toolchain digests
- exact opened-source and compiled-package sets
- SCC and reverse-dependent invalidation sets
- deterministic dispatch and commit orders
- recursive, fallback, and unrelated-read counters
- recovery policy and atomic publication generation
- `ScvCompileSnapshotV1` revision, tree, canonical inventory, object, and
  lifecycle digests
- `ScvFrozenSourceProviderV1` source-open trace and zero live-worktree reads
- snapshot lease, staging, publication, cleanup, and recovery receipts
- `ScvCompileBridgeReceiptV1` trigger/mode/internal-write/diagnostic evidence
- separately framed raw content and semantic/export/initializer/provider digests
- pre/post Git index, ref, HEAD, lock, and history-mutation evidence
- owned-write inventory beneath ignored `build/scv/compile/`

## Traceability

| Requirement | Scenarios |
|---|---|
| `PSI-REQ-001` | explicit closure, unreadable unrelated tree, lazy TLDR/SMF metadata reuse, package action/archive hit |
| `PSI-REQ-002` | direct/indirect invalidation, generated source/output refusal, config/build-tag variants, SCC invalidation, private-body export cutoff |
| `PSI-REQ-003` | deterministic independent scheduling, daemon warm reuse, clean/warm reproducibility |
| `PSI-REQ-004` | missing/stale/corrupt/tampered refusal, bounded rebuild, two crash points, no hidden fallback |
| `PSI-REQ-005` | snapshot admission, concurrent-edit isolation, drift/new build, creation/cleanup crash recovery, provenance, no live fallback |
| `PSI-REQ-006` | implicit quiet compile, event-driven index update, internal write boundary, Git non-mutation, concise diagnostics, atomic GC |
| `PSI-REQ-007` | daemon generation/workspace isolation, remote local admission, remote poisoning refusal |
| `PSI-NFR-001` | all scenarios require zero recursive scans and unrelated reads where applicable |
| `PSI-NFR-002` | deterministic scheduling, action/archive/header reuse, daemon warmth, cross-mode reproducibility |
| `PSI-NFR-003` | all SCV scenarios require immutable active-build identity and atomic snapshot lifecycle |
| `PSI-NFR-004` | comment-only and whitespace-only semantic reuse scenarios |

## Implementation Handoff

The executable is expected red until `PSI-IMP-001` through `PSI-IMP-023` in
the test plan are closed by their production owners. The SPipe checker must not
implement package discovery, invalidation, scheduling, metadata admission, or
receipt generation itself.

## Evidence Integrity

The checker must consume artifacts emitted by the production compiler/index
owner. Source inspection, a fixture-only graph implementation, mocked schedule,
or a test-created success receipt cannot satisfy any scenario. Missing evidence
is a failure, not a skip.

## Freshness

This manual mirrors the executable scenario names and assertions as of
2026-09-02. SPipe/docgen execution is not claimed because the admitted
self-hosted runtime required to execute and regenerate this manual is currently
unavailable.
