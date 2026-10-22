# Qualify the Windows Server Simple Container provider

Status: BLOCKED. Priority: P1. Owner: Windows container integration.

The shared `ContainerHostCapabilityV1`, `RuntimeIdentityV1`, and
`RuntimeOperationV1` contracts exist, but there is no Windows HCS provider or
live Windows Server fixture in this worktree. Do not report a Windows container
from Podman Machine, a CLI version probe, or a Linux guest VM.

Process isolation is selected for this native Windows route; client privilege
policy remains to be selected from
`doc/02_requirements/feature/simple_container_cross_host_options.md`.
Implement a Windows provider through an authorized containerd/runhcs V1/HCS
boundary. Containerd/shim owns HCS handles; the Simple leaf owns client
connection, generation-bound journal, and validated native IDs. Bind each
common operation to the exact native compute-system identity and attempt.
The process-specific V2 shim is documented as coming soon, so it cannot be an
initial dependency. Reject HostProcess workloads, which lack the required
filesystem and process isolation.
The process-only provider does not require the Hyper-V role. Probe the Windows
Containers feature, containerd/runhcs/HCS availability, and authorization as
separate facts.
Record the Windows host build, compatible immutable Windows image digest,
provider version, caller identity, and explicit process isolation mode in a
bounded SDN receipt. A process-isolation incompatibility must fail closed;
Hyper-V/VM substitution is outside Simple Container.
Use the current host/image matrix: Server 2025 can run process-isolated 2025
or 2022 images; older Server releases require their listed compatible images.
Windows 11 process isolation is a separate developer-preview lane: qualify
Server 2022 images and, on compatible 24H2-or-later hosts, Server 2025 images
with an explicit process request and observed no-VM mode. Do not use that
result to close the Windows Server production TODO.

On a Windows Server host, use a source-matched self-hosted Simple runtime to
run the focused contract and native system specs. Under a selected delegated
client policy, prove an ordinary client has only the scoped create, observe,
and destroy authority needed for its own workload; a second unauthorized
identity must fail create, inspect, and destroy. Under a strict rootless policy,
leave unsupported native launch unavailable. Exercise create, start, wait,
stop, and destroy against a pinned Windows image with a unique output marker
and chosen nonzero exit. Retain the native identity, exact task exit, bounded
output, and fresh exact-identity absence after destroy. Reject wrong image or
host tuple, stale attempt/generation, timeout, wrong isolation class, failed
cleanup, and an unmounted host-sentinel read. Reject a Hyper-V request before
native create; only process-isolated evidence can close this TODO.

Acceptance: the selected Windows route launches a real Windows workload,
returns its native exit, enforces the selected client authority, and destroys
the bound compute system. Host discovery or mocked contract tests alone cannot
close this TODO.

Related: [process-container requirements](../../02_requirements/feature/windows_server_process_container.md),
[implementation plan](../../03_plan/agent_tasks/windows_server_process_container.md),
[focused system test plan](../../03_plan/sys_test/windows_server_process_container.md),
[Windows research](../../01_research/domain/windows_server_process_container.md),
[Windows architecture](../../04_architecture/windows_server_process_container.md),
and [cross-host qualification](simple_container_cross_host_qualification_2026-09-26.md).
