# Simple Container cross-host qualification

Status: BLOCKED pending the selected no-admin policy, source-matched Simple runtime, and accessible Windows Server, Linux, FreeBSD, and macOS fixtures.

The shared `RuntimeIdentityV1`/`RuntimeOperationV1` lifecycle contract and SDN capability receipt must be used by the SimpleOS and hosted providers. The provider owns native mutable state; copied capability data is descriptive, never authorization. A workload result needs a real process/task exit, exact attempt identity, bounded output, cleanup, and fresh absence evidence. A host probe alone cannot pass this TODO.

Product/default follow-up: Simple Container is the API on every supported OS.
The current Linux OCI leaf defaults to Podman only as an interim engine. Add
and qualify an in-tree rootless Simple Linux provider, then change the Linux
default after lifecycle, isolation, resource, cancellation, recovery, and
exact-ID cleanup parity pass on a live host. Retain Podman as an explicit
fallback. Windows must use its native process-isolated HCS provider rather
than Podman or a Linux VM. Track this default switch here alongside the
platform qualifications; do not infer it from a successful Podman preflight.

Platform acceptance:

- Linux: rootless Podman user namespace with real create/start/wait/stop/destroy, delegated cgroup behavior where required, and a non-root caller.
- Windows Server: process-isolated Windows containers through an authorized HCS/containerd boundary, with host/image compatibility and an unprivileged client under the selected delegation policy. Reject Hyper-V/VM substitution.
- FreeBSD: OCI/Podman jail route with explicit root authority, or a selected delegated service/VM design. FreeBSD's current native jail route must never report rootless merely because the client has no administrator prompt.
- macOS: run macOS workloads directly on macOS through a qualified native App Sandbox provider. Record signature/entitlements, actual sandbox denial, native exit, and cleanup. SimpleOS workloads run only on SimpleOS.
- Build and container scripts: emit versioned, bounded SDN receipts with distinct schemas and reject malformed input. The distributed-build preflight receipt remains a prerequisite, not a live two-worker PASS.

Research, design, implementation ownership and proposed tests: [parallel plan](../../03_plan/agent_tasks/simple_container_cross_host_parallel_2026-09-26.md). A PR for the prior handoff has not been published because GitHub writes are blocked in this session; do not merge this larger feature before review and executable platform evidence.

The Linux lifecycle and non-root qualification have a separate [host TODO](simple_container_linux_rootless_qualification_2026-09-27.md) so they can be completed on a Linux machine without conflating a capability probe with a managed workload.

Windows Server [HCS qualification](simple_container_windows_server_qualification_2026-09-27.md), FreeBSD [jail qualification](simple_container_freebsd_jail_qualification_2026-09-27.md), and [native macOS qualification](native_macos_simple_container_2026-09-27.md) have separate host TODOs. Each requires a source-matched Simple runtime and live native identity, exit, authority, isolation, and cleanup evidence. SimpleOS remains a separate native kernel provider.

Knowledge routing is also pending: `doc/00_llm_process/knowledge_registry.sdn` has no exact feature route for this lane. Add its route and selection receipt only after coordinating ownership of that already-dirty registry.
