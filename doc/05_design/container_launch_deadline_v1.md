# Container launch admission deadline

The common Simple Container API carries `ContainerEffectDeadlineV1` into its
Linux Podman and Windows Docker adapters. The trusted Host consumer constructs
it only after verifying the signed grant and approval, using their minimum
expiry. It binds the semantic request digest, the retained request's operation
ID, and explicit launch actions. The operation ID remains separately bound
because the provider semantic request digest deliberately excludes it.

The common constructor validates data; it does not authenticate a signature.
Remote packets cannot establish authority merely by supplying this structure.
The action set is limited to `create`, `start`, `exec`, and `attach`. Read and
reconciliation operations have their own authorization. Stop/destroy require
their own live authority or retained explicitly authorized lifecycle ownership.
An expired launch grant neither permits destruction nor releases capacity.

`container_effect_remaining_ms_v1` takes an explicit actual Unix-ms sample from
the platform owner. It rejects invalid/mismatched context, a failed clock sample,
and time at or after expiry. Its positive remaining value is a launch-admission
window, not a running-process timeout. The separately signed duration controls
process lifetime; expiry or heartbeat loss never becomes an automatic kill.

Managed provider paths must repeat their real clock check after native identity
observations and immediately before launching. A leaf check alone cannot cover
the subsequent process-governor wait or fork setup. The shared captured-process
owner therefore also checks after acquiring its slot and at native pre-exec;
the streamed broker carries the canonical absolute deadline and checks before
group start and actual child exec. Neither path may silently fall back to an
unguarded process runner. These owner integrations and common API consumer
composition are prerequisites for claiming final-exec enforcement.

The Linux managed create/start route calls
`process_run_bounded_admitted_v1` with the absolute deadline after its own
policy observation and clock check. A capture error can occur after the native
effect has begun. Output-limit results are also uncertain failures, even if an
exit field happens to be zero. The provider retains its bound request and uses
its existing exact-identity recovery path; neither error proves absence.

Existing unqualified local provider calls retain their existing policy. The
managed policy path requires an explicit deadline for new launches. Scripted
providers have an explicit bounded clock-sample seam for deterministic unit
tests; production instances reject attempts to install that seam. No sleeps or
production fake clock are introduced.

Evidence is source-only until an admitted runtime is available. The common five
cases cover identity/action scope, expiry/clock failure, exclusion of lifecycle
authority, tampered contexts, and signed integer bounds. Provider cases cover
expiry after earlier Host verification, policy-observation ordering, missing
context, no effect consumption, and preservation of separately signed lifetime.
Native captured and streamed pre-exec tests are owned by the process-owner
lanes. No compiler retry, installation, live backend, or suite PASS is claimed.
