<!-- codex-design -->
# Native macOS Simple Container detail design

`MacOsNativeSandboxProviderV1` will own one signed helper process and one
`RuntimeIdentityV1` attempt at a time. It takes an immutable macOS executable
pin, a selected workspace, a compiled policy, bounded argv/env, output caps,
and a deadline. It never accepts a caller-supplied PID or exit code.

Before launch, verify the helper and child code signatures and their App
Sandbox/inheritance entitlements, executable digest and Mach-O architecture, selected workspace,
and supported policy subset. Reject any policy requiring Linux namespaces,
per-attempt mount roots, or isolation the helper cannot provide. Keep the
helper executable and process lease pinned across launch. Check the actual
running helper sandbox state in the live fixture; a static entitlement alone
is not runtime proof.

The provider serializes one attempt for its helper identity. The signed helper
launches the workload inside its inherited sandbox, and the process owner
observes the native start identity, bounded output, terminal status, and
reaping. `RuntimeOperationV1` is published only after exact identity checks.
The existing hosted process-observation V3/V4 owner reports unavailable on
macOS; this paragraph describes a required new Mac owner, not current code.
An independently launched app or XPC/launchd service needs an authenticated
request channel. A directly spawned inheriting helper cannot install an
independent workload sandbox inside an already sandboxed parent.
Cancellation closes admission, stops the owned process group, and waits for
fresh absence. The first route admits only a signed single-process workload;
it must enforce a no-detach/no-child policy and test a child that attempts to
leave the group. If that policy cannot be enforced on macOS, the provider must
report launch unavailable for untrusted workloads. An uncertain native result
stays blocked, never becomes exited or destroyed. A new attempt receives a
new generation and cannot adopt an old receipt.

The SimpleOS sibling keeps `ContainerWorld` and scheduler/IPC authority. Both
siblings use the same common value contracts and SDN codec, but do not share
host calls or native handles. App Sandbox is app-scoped; the first release is
single-workload, same-owner only until separate-attempt isolation evidence
exists. No VM path is in scope.
