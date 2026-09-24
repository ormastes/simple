# macOS-hosted SimpleOS container route

**Superseded 2026-09-27:** This VM route was rejected by the user's corrected
requirement. Use [native macOS and SimpleOS architecture](native_macos_simple_container.md).
The content below is historical and must not be used to claim Simple
Container support on macOS.

The host runs one SimpleOS VM per attempt. It verifies an immutable guest image,
selects `MacQemuHostV1` and a sealed QEMU plan, then opens a private bounded
command channel. The guest owns `ContainerRuntime` and
`SimpleOsContainerProviderV1`; it alone can bind a real kernel task and
reconcile exit. A host QEMU PID, serial boot marker, or process exit is never
the workload result.

`std.common.contracts.container.guest_v1` is the shared identity boundary.
The host sends `GuestContainerAttemptV1` with physical/guest OS, VM class,
guest boot ID, attempt identity, image/workload/policy digests, and nonce. The
guest returns `GuestContainerObservationV1` with that binding plus its native
task ID and kernel-exit observation. The pure validator rejects stale/mismatched
values and requires the running/exited pair to name the same positive kernel
task ID. It does not authenticate transport or launch anything; the eventual
host provider must own a private endpoint and verify a fresh boot before it can
use an observation as evidence.

The source-only guest dispatcher in
`src/os/services/container/macos_simpleos_guest_dispatch_v1.spl` now owns one
attempt over `SimpleOsContainerProviderV1`. It validates the boot, image,
policy, workload and architecture claims before start, then obtains running
and exited observations from the provider's scheduler-backed task. The future
boot service must supply independent image and policy measurements and the
kernel-owned context; echoing request fields is not a measurement. The
dispatcher is not yet wired to a host channel or boot entry. The provider's
managed launch currently imports a removed loader function, tracked in
`doc/08_tracking/bug/simpleos_managed_container_launch_authority_mismatch_2026-09-27.md`.
Repair must use the authenticated loader token path before a live guest can
claim a task exit.

The next vertical slice must add, in order:

1. A bootable SimpleOS image with the container service and a guest command
   dispatcher wired to the real scheduler/context.
2. A bounded authenticated host/guest channel and versioned one-request
   protocol with exact bytes, frame limits, nonce freshness, monotonic
   lifecycle transitions, architecture/ABI matching, deadlines, and cleanup
   on either-side failure.
3. A macOS host provider that verifies the image and plan, starts QEMU, obtains
   a fresh boot ID, sends one request, and observes actual guest task exit.
4. An explicit `virtual-machine` Pod/Job placement path and a live macOS test.

Existing `src/os/qemu_cli_plan_v1.spl` is inspect-only. Existing
`src/app/vm/qemu_manager.spl` is a general SSH QEMU manager, not a SimpleOS
container transport. Neither can be treated as the missing provider.

Related research: `doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`
§4, and `doc/02_requirements/feature/dist_build_scheduler.md` REQ-013.
