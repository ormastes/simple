# macOS SimpleOS guest container live route

**Superseded 2026-09-27:** This VM-backed route is not the selected Simple
Container design. The active Mac TODO is
[native_macos_simple_container_2026-09-27.md](native_macos_simple_container_2026-09-27.md).
The historical VM acceptance below must not close native Mac work.

Status: open, P1. Owner: SimpleOS container / macOS host integration.

The pure attempt and observation boundary is in
`src/lib/common/contracts/container/guest_v1.spl`. A source-only guest
dispatcher is now in `src/os/services/container/macos_simpleos_guest_dispatch_v1.spl`;
its focused spec has not run on a source-matched Simple runtime. To complete
the user's macOS request, implement the private host/guest channel, verified
QEMU image boot, real kernel
exit receipt, and explicit VM Pod/Job placement in the order listed in
`doc/03_plan/agent_tasks/macos_simpleos_guest_container.md`.

Acceptance: one macOS host launches a SimpleOS VM, runs a real managed workload
through `SimpleOsContainerProviderV1`, returns an exit from the kernel task, and
destroys the VM. Wrong boot/nonce/digest, missing image, timeout, and VM exit
must fail closed. The focused pure spec must run on a self-hosted Simple binary.

Current local blocker: no SimpleOS VM image was located in `build/os`; the
focused test runner dropped its child before running any assertion. Neither
condition proves the provider's correctness.

On 2026-09-27, `sh scripts/check/check-macos-simpleos-container-host.shs --sdn`
recorded Darwin arm64, source commit `664c80efda56bbb6903e4e427434e755cb430094`,
QEMU aarch64 digest `391e2408279adc383d36dd61bc4a820f62ec5ec9d2ed5b9e7dd8ad6b835a32ea`,
and HVF availability. It returned `BLOCKED` because no pinned SimpleOS image
was supplied. The retained diagnostic receipt is
`build/handoff/macos-simpleos-container-host-2026-09-27.sdn`. OrbStack still
reported `Stopped`; both Docker Desktop and default contexts denied API access
from this workspace. These are host diagnostics, not a guest boot or task exit.

The executable preflight contract test
`test/00_unit/scripts/macos_simpleos_container_host_spec.shs` passed on
2026-09-27. It checks a pinned-image preflight, missing image, wrong digest,
and symlink rejection with a controlled QEMU/HVF fixture. This is a shell
contract test only; the TODO remains open until the real VM, kernel task exit,
and destroy evidence above exists.

The guest's managed workload launch path currently imports a removed loader
entry. [Bug 355](../bug/simpleos_managed_container_launch_authority_mismatch_2026-09-27.md)
tracks the authenticated loader repair and source-matched kernel task-exit
evidence. A guest dispatcher alone cannot qualify this route until that
launch path works.
