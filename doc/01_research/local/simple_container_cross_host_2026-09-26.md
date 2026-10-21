<!-- codex-research -->
# Simple Container cross-host: local research (2026-09-26)

## Scope and ownership

This research covers a shared Simple Container admission contract and qualified host leaves for Linux, Windows Server, FreeBSD, and a macOS fixture. The fixed shared interface, file ownership, and evidence vocabulary are in `doc/03_plan/agent_tasks/simple_container_cross_host_parallel_2026-09-26.md`. The user has not selected the privilege model. This document records facts and gaps, not a support claim.

The SPipe common package was located at the legacy `.spipe/spipe` route; its research skill and wiki/skills indexes were read. `doc/00_llm_process/knowledge_registry.sdn` has a `src/os/services` layer route, but no exact `simple_container_cross_host` feature route and no `src/lib/common/contracts/container` or `src/lib/nogc_async_mut/container` route. A feature knowledge-selection receipt therefore cannot truthfully claim an exact route. The registry gap belongs to the coordinating owner; this lane owns only the four research/options files.

## Code map

| Surface | Observed behavior | Implication |
|---|---|---|
| `src/lib/common/contracts/container/runtime_v1.spl` | Pure `RuntimeIdentityV1`, `RuntimeOperationV1`, phases, probe/intent values, and transition oracle; identity includes attempt, provider generation, operation ID, native ID, and node boot ID. | Reuse the envelope and keep native mutable state in each provider. |
| `src/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1.spl` | Existing Linux OCI provider defaults to Podman; probes engine health and rootless evidence, validates digest-pinned images and bounded policies, uses argv-based process facade, persists/rechecks intent for recovery. Docker is an explicit alternative. | Do not edit this dirty provider in this research lane. A positive probe is distinct from live isolation, networking, limit, and cleanup proof. |
| `src/os/services/container/container_runtime.spl` and `runtime_provider_v1.spl` | `ContainerRuntime` launches through the SimpleOS scheduler and reconciles a bound zombie task. The adapter wraps one live launch in the common operation envelope, but declares no recovery or logs. | SimpleOS is a separate guest/kernel route, not a host OCI implementation. Keep its scheduler/context authority local. |
| `src/os/services/container/container_manager.spl` | Owns the local container/Pod world and lifecycle state. | Shared contract should carry copied values, leaving the manager/provider as mutable owner. |
| `scripts/check/check-dist-build-host-handoff.shs` | Emits human-readable `dist-host-handoff` lines; checks Linux/Docker and cgroup leaf creation only. | New SDN receipt must retain this human output and identify itself as preflight, not live launch proof. |
| `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1_spec.spl`, `test/01_unit/os/services/container/runtime_provider_v1_spec.spl` | Existing provider and SimpleOS adapter unit fixtures. | Add focused pure admission tests and later live provider tests without relabeling scripted tests as host qualification. |

## Prior design and current evidence

`doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md` already distinguishes `native-container` from `virtual-machine`, calls for exact Windows host/image compatibility and FreeBSD jail evidence, and warns that macOS Linux containers use a VM. Its later addendum says Windows process isolation needs an Administrator-capable route and FreeBSD jail creation needs root. The fixed parallel plan narrows macOS work to fixture verification. The distributed-build plan at `doc/03_plan/compiler/build_system/dist_build_scheduler_2026-09-25.md` records a Docker Desktop Linux ARM64 fixture from a macOS parent, but explicitly does not claim a Simple provider run, native Darwin container, or two-node build.

## Research gaps and required proof

No Windows Server or FreeBSD provider source was found in the inspected container module paths. A Windows leaf must prove effective process versus Hyper-V isolation, HCS/runtime identity, a supported host/image tuple, process exit, and teardown. A FreeBSD leaf must prove jail/ocijail identity, scoped launch authority, requested VNET/PF and resource enforcement, and cleanup. Linux rootless qualification needs a real Podman launch and effective namespace/cgroup/network/storage evidence. The macOS fixture can verify a Linux VM-backed container route only under `virtual-machine` and must not advertise a Darwin `native-container`.

The fixed `ContainerHostCapabilityV1` fields (`host_os`, `guest_os`, `provider_id`, `isolation_class`, `client_privilege`, `admin_setup`, `launch_capable`, `reason`) can express these distinctions. `client_privilege=delegated` is launch-capable only after a separately owned broker proves scoped authorization. A pure capability fixture or installed engine alone cannot set a live PASS.
