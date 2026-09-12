<!-- codex-design -->
# Windows Full Bootstrap and Toolchain Suite Detail Design

## User Interface Scope

No new TUI or GUI is introduced. Existing DevHub/IDE surfaces are exercised through their production commands. Evidence uses typed text/protocol/exec/binary/artifact captures; GUI-unavailable conditions remain BLOCKED with an exact resume command.

## Records

- `BootstrapPhaseReceipt`: immutable phase identity and authority record described by the architecture.
- `ToolPrimaryFeatureReceipt`: one exact interpreter/native primary-feature observation.
- `SuiteAcceptanceRow`: one suite classification with evidence, performance, owner, prerequisite, and resume command.
- `DeploymentRollbackReceipt`: one atomic deploy/rollback transaction.
- `BoundedStreamEvidence`: head/tail/omitted bytes, total bytes, digest, exit, timeout, and descendant-pipe status for stdout/stderr.
- `PerfEvidence`: exact subject/fixture/machine/load, warmups, samples, startup, p50/p95/max latency, and max RSS.

Canonical serialization is SDN with schema/version and closed fields. Unknown fields, missing authority fields, malformed digests, relative/symlink subject paths, duplicate row identities, or nonterminal classifications reject.

## Phase Algorithm

1. Resolve conflicts, capture tracked-file count, freeze exact source and base, and verify no marker/content drift.
2. Create an isolated generation root under `build/bootstrap/evidence/windows/<generation>/`; convenience `latest` pointers are non-authoritative.
3. Run the canonical combined Stage 1/Stage 2 MSVC trust-root command with default diagnostics off, `SIMPLE_NATIVE_INCREMENTAL=1`, a stable generation cache, and a required positive reuse receipt.
4. Seal build/provenance only after artifact identity, parent, environment, command, and logs validate.
5. Run compiler, interpreter/authenticated execution, interpreter-mode tools, native tool builds, and primary-feature oracles against that exact hash.
6. Admit the phase only when every required row is PASS and every unavailable row is explicitly BLOCKED/UNSUPPORTED without contributing to PASS.
7. Fetch/rebase, compute invalidated inputs, rerun only invalidated gates, exact-head review, and publish linearly.
8. Produce the next typed planner receipt and repeat for Stage 3 and Stage 4.
9. Run Stage 4 essential tools, post-bootstrap SSpec, named integrated suites, and performance evidence.
10. Deploy the immutable generation, smoke it, prove compare-and-select rollback, then select the candidate again only through a new valid transaction.

## Suite Matrix

Required rows cover compiler, interpreter, `check`, test runner, lint, duplicate-check, native-build, MCP, LSP MCP, SPipe execution/docgen, DevHub, Caret, IDE, T32 MCP, and T32 CLI. MCP/LSP protocol evidence is initialize -> initialized -> tools/list -> representative semantic request. IDE requires launch plus edit/check behavior. T32 hardware-free help/version/init is required; provider-dependent behavior is separately blocked when TRACE32 is absent.

## Publication and Review

The tested source fingerprint must match the publication head. A rebase invalidates source-dependent receipts. Protected review binds repository, PR/head, session, reviewer model/effort, changed-path manifest, evidence digests, expiry, and zero P0/P1. `SPipe Self Review Admission` is a required check, never author or independent approval.

## Error Model

Use terminal `PASS`, `FAIL`, `UNSUPPORTED`, `BLOCKED`, and `INCONCLUSIVE`. Timeout, missing verdict, binary drift during a run, or high-load distortion is INCONCLUSIVE rather than product FAIL. FAIL rows carry exact command/input fingerprint and cycle count. BLOCKED rows require reason, owner, prerequisite, artifacts, and resume command.

## Observability

Record phase timestamps/durations, cache reuse receipts, process-tree peak RSS, bounded streams, executable identity before/after every run, protocol frames, artifact digests, invalidation reasons, and deployment pointer transitions. Debug diagnostics are opt-in failure evidence and never performance or promotion evidence.

## Implementation Strategy

Prefer existing bootstrap/admission/suite/deployment owners. Add the smallest common Simple facade only for a contract not already represented; do not add raw `rt_*` shortcuts. Scripts adapt host execution and never duplicate receipt semantics. Initial executable SSpec helpers remain explicit fail-fast placeholders until their production owner is wired.
