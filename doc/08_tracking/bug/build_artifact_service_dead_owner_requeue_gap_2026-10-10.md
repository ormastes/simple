# Build artifact service has no dead-owner reclaim transition

Status: OPEN. Severity: reliability gap in the service API; full build/test
runner deadlock is **not established**. Source base:
`c48d5fb07cc5d75777c63252f2e0659b9bd8e248`; unchanged at inspected release
`f92764f2b97f99de8b60db2d454208de55564be2`.

`src/lib/compiler_artifact_service/service.spl:artifact_service_claim_v1`
selects only `queued` entries. After it returns `leased`, another claim leaves
that entry leased regardless of the new owner/generation. If its worker dies,
there is no public reclaim/requeue transition. `artifact_service_cancel_v1`
produces terminal cancellation; enqueue of the same action returns unchanged.
Repeated claim/enqueue/cancel cannot implement safe retry after owner death.

`src/app/test_runner_new/runner_lifecycle.spl` provides tracked child spawning,
cleanup, process-governor slot release and parent-heartbeat checks.
`process_tracker.spl` tracks PIDs/containers. These helpers do not carry the
artifact action ID, owner-instance identity or lease generation into a service
requeue operation. `cache/lease/lease.spl` protects GC roots, not build execution.
The existence of those helpers is therefore not evidence that this service's
lease recovery is wired into the actual runner.

The inspected c48 `tracker_check_heartbeat_alive(timeout_ms)` explicitly returns
`true` as a runtime-compatibility stub, and `tracker_send_heartbeat` records zero.
`runner_lifecycle.lifecycle_check_parent_alive` delegates to that API. Until a
production caller/provider connection is established and exercised, these
functions cannot serve as the proposed death authority. This observation does
not establish reachability from every current `simple test` mode.

Separately, source-bound bootstrap replay reproduced wrong-action publication
and stale-owner poisoning; the narrow production fix preserves the live entry
for those unauthorized completions. It does not add crash recovery. Exact
RED/GREEN evidence and source bindings remain in
`build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/formal/`.

Design: `doc/05_design/build_artifact_service_owner_recovery.md`. Admission needs
real worker death/lock-release evidence, parent-authoritative generation fencing,
a rejected late completion, exactly one admitted retry and successful output
publication. Time elapsed or a reused PID alone must never justify reclaim.

Until that production path is implemented and exercised, unconditional
no-stall claims remain false. Progress is conditional on fair scheduling,
finite dependencies, sufficient resources, eventually completing providers,
and authoritative owner-death detection.
