# Test runner container runtime missing from async facade

Status: source repair applied locally; native verification UNRUN.

The frozen Phase3 diagnostic for `runner_lifecycle.spl` fails because
`std.test_runner.process_tracker` does not export `tracker_container_runtime`.
The sync owner already implements the function and the lifecycle imports and
calls it at two sites. The async forwarding facade omitted it.

Evidence: `build/native_probe/build-runner-review-20261011/test-failed14-continuation/TERMINAL_REVIEW.json`, entry13.

Repair: add the existing function to the explicit async export list. No new
implementation, mutable state, cache or process operation is introduced.
This source observation does not establish runtime performance neutrality.

Regression fixture: `test/fixtures/compiler/process_tracker_runtime_export.spl`
imports through the repaired facade and calls the real owner. It accepts only
the documented docker/podman/none results, probes availability, and never starts
or stops containers. Compile/link/run checks remain UNRUN and must use bounded
execution: the owner may probe both runtimes, each with a five-second timeout.

Admission requires native import resolution and execution, no unresolved-owner
fallback, and relevant performance/memory qualification before release. Existing
successful diagnostics must not be replayed for this repair.
