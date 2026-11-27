# Separate-process metadata controller

Status: **NOT_RUN — awaiting verification**. This manual is authored from the
executable assertions; it is not SPipe-generated or passing runtime evidence.

- Spec: `test/03_system/app/orchestrator/feature/local_controller_process_spec.spl`
- Oracle: `test/fixtures/orchestration/local_controller_process_native_probe.spl`,
  `local_controller_process_checks(binary)`
- Authored requirement labels: CARET-01, OPS-01, ORCH-02, from
  `doc/02_requirements/feature/caret_distributed_orchestrator.md`. These labels
  record partial traceability rather than verified requirement completion.

## Setup

The spec expects a separately compiled executable at
`build/orchestrator-controller-cli/simple-orchestrator`. The standalone diagnostic
probe takes its compiled orchestrator path as one explicit argument. Neither the
spec nor probe builds an executable or supplies a successful fallback.

Run from the repository root with these existing inputs:

- `test/fixtures/orchestration/caret_agent_session.sdn`
- `test/fixtures/orchestration/caret_policy_catalog.sdn`

The oracle reads the exact session source and computes its SHA-256. It creates
a fresh private parent below `/tmp`; retained state is intentionally available
at the printed evidence path. Every command runs as a new child through the
bounded process facade, with a 20-second timeout and 64 KiB capture budget.
No in-process `orchestrator_command_v1` adapter supplies the result.

## Scenario: retain one immutable Caret request across processes

1. Invoke `local-init <private-parent> controller`. Check exit 0 and a returned
   stateRoot below the private parent.
2. Invoke `submit <stateRoot> controller caret-request-one <session-file> caret
   review-simple`. Check exit 0, status `intent-retained`, request UID
   `caret-request-one` and sourceDigest equal to SHA-256 of the input bytes.
3. Independently read
   `<stateRoot>/journal/desired-input-objects/<sourceDigest>.sdn`. Compare its
   exact bytes to the original source and recompute its hash. This check uses
   the expected content-addressed path, not a store helper or returned object.
4. Submit the identical request in another child. Check the same sourceDigest.
   Inspect it in another child and check the exact digest, assignmentState
   `unbound` and runtimeState `unobserved`.
5. Write changed task content to a separate file, preserving the request UID.
   Submit it and check exit 1 with `desired-input-identity-reused`.
6. Invoke `pin-policy` using the retained UID, catalog and same session selector.
   Check `policy-retained`; repeat in another child and compare catalogDigest.

For every response, check version 1, kind `orchestrator-local-controller` and
executionAuthorized=false. Every successful response also retains the exact
controllerId. Successful non-init responses retain the argument's requestUid.
Error replies preserve the existing V1 contract and are not required to invent
controller/UID fields absent from that contract.

## Scenario continuation: source-bound sticky cancellation

1. Cancel with an incorrect source digest. Check exit 1 and
   `desired-cancel-source-mismatch`.
2. Cancel using the exact original digest. Check `intent-cancelled`; repeat the
   same cancellation in a separate child and check the original sourceDigest.
3. Inspect again. Check desiredState `cancellation-requested`, the original
   digest, runtimeState `unobserved` and terminationObserved=false.
4. Attempt submit and policy pin again. Both must fail with
   `desired-input-cancelled`.
5. Inspect using another controller ID. Check `local-controller-mismatch`.

## Assertion mapping and limits

| Authored labels | Concrete assertions |
|---|---|
| CARET-01 | Exact controller/request identity, immutable source bytes/hash and changed-content refusal |
| OPS-01 | Actual bounded child invocations and repeated journal close/reopen through the executable |
| ORCH-02 | Retained policy/cancellation, refusal to revive cancelled intent, truthful unobserved runtime |

Missing executable, unreadable fixture, wrong exit or mismatched fields causes a
real assertion failure. No checks here launch a host workload, authenticate a
signed execution grant, observe Podman, attest termination or prove process
isolation between controller and host. The approved future dispatch target is
local-inprocess with separate journals; it is not implemented by these metadata
commands. Admitted execution, SPipe generation/maintenance, coverage and full
system acceptance remain NOT_RUN. No build or test run is claimed by this manual.
