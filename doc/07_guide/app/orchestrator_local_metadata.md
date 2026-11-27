# Local orchestrator metadata commands

Status: source merged in PR7578; compiled command roundtrip and admitted SSpec
execution are awaiting verification. Use an explicitly configured, cached
`simple_orchestrator` executable built from `src/app/orchestrator/main.spl`.
No binary is qualified by this guide. Do not substitute a source runner.

## Initialize and retain intent

The administrator supplies an existing trusted parent directory. `local-init`
creates a private child state root and returns its `stateRoot` in canonical SDN.
The same root and controller identity must be used for subsequent commands.

```text
simple_orchestrator local-init <trusted-parent> <controller-id>
simple_orchestrator submit <state-root> <controller-id> <uid> <source-file> <namespace> <name>
simple_orchestrator pin-policy <state-root> <controller-id> <uid> <catalog-file> <namespace> <name>
simple_orchestrator inspect <state-root> <controller-id> <uid>
simple_orchestrator cancel <state-root> <controller-id> <uid> <sourceDigest>
```

For the checked-in example, use
`test/fixtures/orchestration/caret_agent_session.sdn`, namespace `caret`, name
`review-simple`; the catalog is
`test/fixtures/orchestration/caret_policy_catalog.sdn`. Choose and retain a UID
before submission. Reusing it with changed source is rejected. Policy pinning
retains the selected catalog identity. Cancellation requires the original exact
source digest and remains sticky on later submission or policy attempts.

Successful replies use `version: 1`, `kind: orchestrator-local-controller`,
`controllerId`, and, except initialization, `requestUid`. Submission returns
`sourceDigest` and `status: intent-retained`. Inspection reports separate desired,
assignment and runtime fields. This interface always returns
`executionAuthorized: false`; the metadata fixture expects
`runtimeState: unobserved` and `terminationObserved: false`.

An error with `reconciliationRequired: true` may follow a committed metadata
effect. Keep the original root, controller identity, UID and source digest;
inspect that UID. Do not infer rollback from failed stdout, process timeout or
an error reply. The Caret client preserves unconfirmed identity rather than
automatically issuing a new request.

## Evidence and limits

The executable process fixture is
`test/fixtures/orchestration/local_controller_process_native_probe.spl`. It
invokes a supplied compiled controller separately for every command and checks
the retained source file independently. Its mirrored SSpec expects the binary at
`build/orchestrator-controller-cli/simple-orchestrator`; absence fails the test.

These commands retain metadata only. Dispatch, host enrollment/prepare/execute,
provider observation, workload termination and resource release are not exposed
by this admitted controller. A cancelled intent is not proof that a runtime
stopped. Signed dispatch and `inspect-execution` remain design work. See
`doc/03_plan/sys_test/orchestrator_verification_wait_20261107.md` for the exact
pending acceptance gates and recorded compiler blocker.
