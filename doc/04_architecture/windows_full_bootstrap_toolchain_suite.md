<!-- codex-design -->
# Windows Full Bootstrap and Toolchain Suite Architecture

## Decision

Model Windows bootstrapping as a monotonic, receipt-driven promotion state machine:

```text
FrozenSource -> Built(Pn) -> Verified(Pn) -> Admitted(Pn) -> Published(Pn)
                                                        \-> Built(Pn+1)
Admitted(Stage4) -> DeployedGeneration -> RolledBackGeneration
```

A transition consumes immutable inputs and emits a new receipt. It never edits an admitted receipt or snapshot. A later phase may consume only the immediately preceding admitted subject. Publication and deployment are separate authorities from compilation and verification.

## Shared Contracts

`BootstrapPhaseReceipt` binds schema/version, phase, generation, source fingerprint/head/base, target/triple/ABI, subject absolute path/SHA-256, parent path/hash/receipt hash, typed planner receipt, command/environment/toolchain/host identity, isolated output/cache roots, supported capabilities, evidence/log digests, diagnostics mode, timestamps, verdict, reviewer, and publication status.

`ToolPrimaryFeatureReceipt` binds the phase receipt, tool/suite, interpreter or native mode, exact executable/hash, command, bounded stream evidence, behavioral oracle, duration/max RSS, fallback status, verdict/reason/owner/prerequisite.

`SuiteAcceptanceRow` represents required, PASS, FAIL, UNSUPPORTED, or BLOCKED suite state. Only required PASS rows promote; blocked/unsupported rows remain visible and never count as PASS.

`DeploymentRollbackReceipt` binds prior/candidate/deployed/restored generation hashes, compare-and-select state, atomic pointer transition, smoke results, rollback authorization, and operation digest.

## Virtual Capsules

1. **SourceFreezeCapsule** owns conflict-free source identity, tracked-file guard, frozen worktree, base comparison, and exact-head review.
2. **StageBuildCapsule** owns Windows wrapper execution, isolated output/cache, process bounds, and build logs; it cannot admit or publish.
3. **AdmissionCapsule** validates parent, target/reason, source/toolchain/command hashes, and seals a receipt.
4. **Stage3AuthorityCapsule** exposes one facade over Stage 3 manifest write/verify, command snapshot, and sanity modules.
5. **Stage4CandidateCapsule** binds the unchanged full CLI to Stage 3 authority, planner continuation, source roots, policies, and essential-tool evidence.
6. **SuiteEvidenceCapsule** produces typed tool/suite rows and performance evidence but cannot authorize build or deployment.
7. **PublicationCheckpointCapsule** compares with `main@origin`, applies linear history, invalidates digest-dependent evidence, and records pushed SHA/check state.
8. **DeploymentTransactionCapsule** installs one complete immutable generation and atomically switches a single pointer; rollback compare-selects a verified predecessor.

Sibling-private implementation details remain inside each capsule. Public consumers receive only validated receipts or terminal classifications. Scripts are adapters around one shared schema, not competing authorities.

## Ownership

- Build: `scripts/bootstrap/bootstrap-windows.cmd`, `bootstrap-windows.sh`, `bootstrap-from-scratch.sh`.
- Admission: `src/app/build/bootstrap_receipt_main.spl`, planner modules, `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`, and bound validators.
- Stage 3/4: `scripts/check/lib/bootstrap-stage3*` and `scripts/check/lib/stage4-candidate-provenance.shs`.
- Suites: existing essential-tool, post-bootstrap, must-pass, phase-feature, MCP/LSP, and tooling-matrix owners.
- Publication: jj sync flow, push gates, must-check ledger v3, and SPipe self-review admission.
- Deployment: generation transaction, authority verifier, and rollback owners under `scripts/bootstrap/`.

## Startup and Hot Paths

Bootstrap orchestration is maintenance work and may scan its declared source closure once. MCP/LSP and tool-server request handlers may not repeat full-tree scans, source reads, or subprocess startup per request. They reuse admitted interface/index caches keyed by source and binary digests; source/config/tool manifest changes invalidate affected cache entries.

Measure direct binary startup separately from wrappers. Retain warm startup, representative p50/p95/max request latency, peak process-tree RSS, fixture identity, machine/load metadata, and sample count. Default diagnostics remain off during performance evidence.

## Failure and Recovery

- Build failure emits non-authoritative FAIL evidence and no admission/publication receipt.
- Missing, symlinked, stale, duplicated, cross-generation, unsupported, or unauthorized inputs fail closed.
- A crash before sealing leaves temporary output ignored; seal and pointer changes use exclusive creation plus atomic replacement.
- Source/base drift invalidates only receipts whose input digest changed.
- A publication race returns to `FrozenSource`; no unconditional force is allowed.
- Deployment failure leaves the old generation selected. Rollback refuses a mismatched current generation or unverified predecessor.
- Attempt records are keyed by command plus input digest; identical failed commands are not repeated and one issue is capped at three distinct fix cycles.

## Requirement Allocation

- REQ-001/009/011: SourceFreeze and PublicationCheckpoint.
- REQ-002/004: StageBuild and SuiteEvidence.
- REQ-003/006/007: Admission, Stage3Authority, and Stage4Candidate.
- REQ-005: PublicationCheckpoint.
- REQ-008/012/013: SuiteEvidence and attempt ledger.
- REQ-010: DeploymentTransaction.
- REQ-014: versioned documentation/spec/ledger consumers of the same contracts.

NFR-001/002/006/008/009 are admission invariants; NFR-003 is owned by bounded process capture; NFR-004 by the attempt ledger; NFR-005 by suite performance rows; NFR-007 by deployment transactions; NFR-010 by retained reproduction bundles.

## Rejected Patterns

- One mutable output tree spanning phases.
- Path-only or log-only admission.
- A wrapper, Rust seed, raw source, cross-build, or stale deployed CLI substituting for the exact phase subject.
- Suite PASS inferred from process exit without an authoritative verdict/oracle.
- Per-file deploy copies or rollback by loose restoration.
- Author GitHub approval, stale self-review admission, force push, or protection weakening.

