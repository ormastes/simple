# Orchestrator verification wait — 2026-11-07

**Status: AWAITING_VERIFICATION. Verification verdict: WARN; release-ready: false.**
The user requested complete tests/documentation and a verification checkpoint.
Feature expansion stopped before signed dispatch code was written. Maximum CPU
allocation is five cores across all lanes, not five per lane; local push/check
processes share `taskset -c 0-4`. Builds require root's explicit allocation.

## Immutable admitted scope

| Slice | PR / merge | Runtime evidence |
|---|---|---|
| Strict resource/profile foundation | 7544 / `552a52ecb049b4e5d9ee522b8db81f7960b46d1f` | One successful unadmitted focused native probe only |
| Placement, assignment, fence and execute packet prerequisites | 7568 / `1368e5d2adae9d4dcddc075e5b059880b2a10bba` | Packet build blocked before link; no artifact |
| Actual local metadata controller and direct HostConfig decoder | 7578 / `a6dca22ee32da27ff9e45a67ba86ae3ef587074e` | Source reviewed; compiled roundtrip NOT_RUN |
| Modern Caret-to-controller metadata acceptance | 7582 / `490935a4a7cd` | Six scenarios authored; runtime NOT_RUN |

Metadata reviewed source: `16ac902c915f14274fb857c156e0efe758599fc8`.
Public acceptance reviewed source: `2fdcf3338d8`. Historical seed results in
`.spipe/simple_orchestrator/state.md` are not current self-hosted evidence.

## Requirements and executable evidence inventory

The user-selected revision-1 shorthand requirements and NFRs are preserved, with
original source hashes and historical-status caveats, in
`doc/02_requirements/feature/caret_distributed_orchestrator.md` and
`doc/02_requirements/nfr/caret_distributed_orchestrator.md`. CFG-01/02,
ORCH-01/02, HOST-01/02 and CARET-01/OPS-01 labels in the local specs refer to
that selected plan. These are partial assertions, not full requirement coverage.
The older architectural requirements remain in
`doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`,
section 1.2 (ORCH-001 through ORCH-016). This checkpoint maps the already selected
scope; it does not select new requirements or declare the entire requirements set
satisfied. ORCH-01 is not an alias for ORCH-001; the table below relates assertion
intent to the older architecture goals. All specs below are under
`test/03_system/app/orchestrator/feature/`; their authored manuals have the same
basename under `doc/06_spec/03_system/app/orchestrator/feature/`.

| Requirement / accepted constraint | Spec basename | Real oracle and current limit |
|---|---|---|
| ORCH-001 strict SDN; minima and bounded allocation | `resource_profile_foundation_spec` | Actual quantities, overflow boundaries, nested duplicate/selector coordinates and minimum/recommendation/preference decisions; no ledger effects |
| ORCH-004 / ORCH-013 immutable placement | `placement_spec` | Plan/offer identity, host scope, capacity and digest mismatch rejection; pure contract only |
| ORCH-013 stale assignment/cancellation fencing | `controller_workload_fence_spec` | Exact revision and assignment identities, cancellation and stale update rejection; pure contract only |
| ORCH-016 signed execution boundary | `host_execute_request_spec` | Canonical packet, byte caps, full scope and identity mismatch rejection; zero-signature shape fixtures do not authenticate |
| ORCH-001 / ORCH-013 local metadata persistence | `local_controller_process_spec` | Actual compiled child per command, immutable UID/source, independent persisted source bytes/hash, reopen/policy/cancellation; requires external binary |
| ORCH-001 host administrative configuration | `host_config_source_spec` | Real decode, native integers, exact rejection paths/coordinates and UTF-8 byte limit; no native host authority |
| ORCH-001 / ORCH-003 CI decoder compatibility | `resource_set_ci_prefix_spec` | Singleton Job and nested Pipeline values/errors preserve prefixed source locations and unknown/duplicate refusal |
| ORCH-013 / ORCH-014 real public metadata path | `caret_controller_cli_acceptance_spec` | Configured Caret process invokes compiled controller; fresh inspect, durable UID/source audit, replay CURRENT stability, changed-source/wrong-controller/relative-executable/extra-argument refusal |

The first seven specs contain 50 authored scenarios; the public-path spec adds
six. These counts are inventory, not runtime passes or measured branch coverage.
The first seven specs call corresponding
`test/fixtures/orchestration/<basename-without-_spec>_native_probe.spl` entrypoints.
The modern public acceptance helper is
`test/fixtures/orchestrator_acceptance/caret_controller_cli.spl`; its executable
path/hash and private artifact-root inputs are frozen in
`doc/03_plan/sys_test/caret_controller_cli_acceptance.md`. Missing executables
must fail or produce the documented unavailable gate, never a fabricated pass.

## Prior diagnostic evidence

Resource/profile evidence is retained in
`.spipe/simple_orchestrator/resource_profile_foundation_verification_20261107.sdn`.
The successful binary SHA-256 was
`6cb0bb61211d356253e25d6b36390eefbd226d9c3c7624ac7829daca74269088`.
The producer was unadmitted, and invalid-array/cache diagnostics remained. This
does not qualify the admitted SSpec runner, coverage, other contracts or CLI.

Packet failure is retained in
`.spipe/simple_orchestrator/dispatch_dependency_verification_20261107.sdn`.
Producer SHA-256
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`
cannot lower current crypto `Array.fill_span`; the build stopped before linking.
No packet executable or run exists. The changed compiler prerequisite must be
independently established before another allocated attempt. Do not retry the
unchanged producer, roll back secure wiping, import old crypto, or reset the
global cause budget by changing worktree/lane.

## Pending full verification sequence

1. Root admits an appropriate self-hosted producer/runner and allocates bounded
   work within the shared five-core ceiling. Preserve source, producer/runtime,
   cache identity and executable hashes. No seed fallback.
2. Compile the real controller and Caret public entrypoints with the documented
   closure/provider roots. Run the eight scoped specs above once, including the
   real separate-process and modern public-path fixtures. Pure contract tests
   cannot replace these external boundaries.
3. Run the selected full repository suite under the root-owned test plan, with
   failure containment and exact receipts. It has **not run** for these changes.
   Record branch coverage and all skipped/blocked scenarios; no coverage value
   has been measured.
4. Run `check src/compiler`, `check src/lib`, `check src/app/mcp`,
   `check src/app/simple_lsp_mcp`, and the interpreter-mode
   `test/02_integration/app/mcp_stdio_integration_spec.spl` using the admitted
   runtime. Complete the required core runtime and MCP native smoke gates.
   These are NOT_RUN. Packaging was unchanged, so npm publication smoke is not
   newly required by this slice.
5. Generate/maintain the mirrored manuals using admitted SPipe docgen and
   `sspec-maintain scan`, inspect readable steps and zero stubs, and retain the
   resulting receipts. Current manuals are authored, not generated evidence.

Source/provenance/import review, direct-env working/staged guards and executable
spec layout checks passed during source admission. The metadata push passed all
11 blocking gates. These checks are retained evidence, not repeated to simulate
runtime verification. Any source repair requires a new scoped review and only
the affected verification rerun; already-green unchanged criteria are not rerun.

## Explicit full-system gaps

Signed `dispatch` and `inspect-execution`, immutable administrative dispatch
configuration, host enrollment/prepare/execute composition, durable runtime
observations, and actual OCI nonce/native-ID inspection remain absent or pending
their lane owners. Root approved a future explicit `local-inprocess` composition
with separate controller/host journal owners; it is not implemented here and
claims neither remote process isolation nor daemon liveness.

Existing AgentSession UIDs cannot use generic dispatch to bypass desired source,
image or invocation resolution. Real Caret/Mux stream binding, TaskRunner parent
acceptance, unknown-outcome replay, exact absence-before-release, GPU exclusivity
and live no-overcommit enforcement still require end-to-end evidence. Linux
container execution is not inferred from packet decoding. Windows, macOS,
FreeBSD, SimpleOS and cross-host network requirements remain open.

The acceptance lead owns the joint full-system matrix. Sol prepared scoped
inventory/manual updates; Astra reviews source, requirements mapping, manuals and
exclusions; root owns runtime allocation and landing. No release PASS, tag or
publication is authorized by this checkpoint.
