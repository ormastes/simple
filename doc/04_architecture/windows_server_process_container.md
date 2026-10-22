<!-- codex-design -->
# Windows Server process-isolated Simple Container architecture

Status: proposed, 2026-09-27. A live Windows provider does not yet exist.

## Boundary and ownership

The controller requests `windows/windows/native-container`. The Windows provider selects an immutable Windows image and **process** isolation, then validates the installed host build/image pair before create. It never substitutes Hyper-V, a Linux utility VM, a HostProcess workload, or a bare host process. The provider reports a capability only after the feature, runtime, image, and current authority route are all usable. Windows Server is the production target; Windows 11 process isolation is a separate development-preview capability that must pass its own compatibility and mode checks.

Use the existing common values in `src/lib/common/contracts/container/` for admission, identity, and lifecycle. Add a sibling Windows leaf under `src/lib/nogc_async_mut/container/providers/windows/`; it may share pure validation helpers with other leaves but must own Windows policy and runtime calls. The initial platform bridge is containerd plus its available `runhcs` shim. This runtime route is community-supported on Windows Server, while Microsoft supports the Windows container OS components; deployment must disclose that distinction. Containerd/shim/HCS own native handles; the Simple leaf owns a client connection, a generation-bound request journal, copied compute/task IDs, deadlines, and result validation. A later direct HCS/SFFI route needs its own design and measured reason to replace the bridge. HCS's create security-descriptor argument is reserved, so it cannot implement ordinary-client delegation by itself.

| Layer | Owns | Never trusts from a receipt alone |
|---|---|---|
| Common contract | Exact OS/isolation admission, copied lifecycle values | Native process mode or caller authority |
| Windows leaf | Host/image matrix, digest, process mode, allowed mounts/network, task identity | User-chosen container name as HCS identity |
| Runtime/shim | Image layers, scratch, HCS compute/process handles | Simple controller policy |
| Network adapter | Chosen CNI/HCN route, HNS endpoints and their cleanup | Containerd task existence as proof of network policy |
| Optional scoped broker | Authenticated ordinary client and per-attempt authorization | Broad Docker/containerd pipe membership |
| Controller | Requested workload, attempt generation, accepted result | A stale SDN document as permission |

The current `RuntimeProviderV1` trait exposes probe only; create/start/wait/stop/destroy remain Windows-leaf operations returning `RuntimeOperationV1`. Each result is accepted only when pod UID, attempt, provider generation, boot identity, operation ID, and runtime compute/task ID match. A timeout leaves state uncertain and starts exact-ID reconciliation; it cannot advance the common transition oracle. Only the owner commits validated observations. Child operations return copied bounded values; native handles never cross into common contracts.

## Admission and privilege

Preflight separates host edition/build, Containers feature, containerd/shim/HCS health, image compatibility, process-isolation support, and current caller authorization. The Microsoft matrix allows Server 2025 with Server 2022 or 2025 images; it separately lists Windows 11 with Server 2022 and certain Windows 11 builds with Server 2025 for development. These are enumerated pairs, not a blanket cross-version grant. Pin image digest and check image OS metadata against the live host matrix. Verify the actual runtime mode after create as well as the requested mode, and record evidence that no utility VM was used; delete and report a mismatch.

The client privilege choice is still pending. If strict no-admin execution is selected and no proven user-level Windows runtime exists, return `launch_capable=false`. If one-time provisioning plus an ordinary client is selected, a dedicated service may authorize only allowlisted image digest, command, mounts, network, resource limits, attempt, and owner identity. It must not expose unrestricted containerd/Docker access. Workloads run as `ContainerUser` by default, with mount ACLs checked separately. A process container shares the host kernel and is unsuitable as the sole boundary for hostile tenants.

## Lifecycle and failure behavior

1. Freeze the request and persist an intent before creating native resources.
2. Resolve pinned image layers/scratch and create an allowed HNS endpoint through the selected CNI/HCN adapter; request process isolation explicitly.
3. Create and start; record the runtime's actual compute/task identity. Reject a HostProcess or VM observation.
4. Wait for the bound process, capture bounded output and exact exit code, and commit the copied result.
5. Stop/terminate on deadline, then destroy only that bound identity and its bound HNS endpoint; query fresh native absence before marking destroyed.
6. On disconnect, timeout, restart, or cancellation, reconcile the recorded exact ID and generation. Never scan/adopt arbitrary containers by name.

Probe once per provider session; cache static runtime/image metadata by digest and runtime version. Invalidate on service reconnect, host reboot, image replacement, or provider generation change. Authorization is checked on every mutation. Measure warm probe, create/start, wait, destroy, peak RSS, and refusal reasons on a real Windows Server fixture. Numeric budgets await selected NFR targets.

Sources and local evidence: [domain research](../01_research/domain/windows_server_process_container.md), [local research](../01_research/local/windows_server_process_container.md), [detail design](../05_design/windows_server_process_container.md), [test plan](../03_plan/sys_test/windows_server_process_container.md).
