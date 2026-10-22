<!-- codex-design -->
# Windows Server process-container detail design

Status: proposed interface and sequence, 2026-09-27. No Windows implementation or live test is claimed.

## Windows leaf values

Keep the common `ContainerHostCapabilityV1`, `RuntimeIdentityV1`, and `RuntimeOperationV1` unchanged. The proposed Windows leaf owns these copied values:

| Value | Required fields |
|---|---|
| `WindowsProcessContainerRequestV1` | pod UID, attempt, generation, operation ID, immutable image digest, image OS build, argv, `process` mode, mount/network/resource policy IDs, deadline |
| `WindowsProcessContainerProbeV1` | Server edition/build/revision, Containers feature, runtime/shim versions, authority state, compatible image availability, reason |
| `WindowsProcessContainerObservationV1` | engine and boot identity, actual compute/task ID, observed process mode, image digest/build, phase, exit code, bounded stdout/stderr, HCS/runtime reason |

The leaf constructor validates nonempty IDs and deadlines, a Windows image, a digest, known policy IDs, and the current host/image matrix before any mutation. It does not accept a generic `native-container` capability as proof of process mode. Runtime and broker connection objects remain private to the leaf. If Simple SFFI is later needed for direct HCS calls, keep the C boundary small and leave policy in `.spl`.

## Operation sequence

`probe` is read-only. `prepare` freezes a request and persists an owner-scoped intent. `create` requests process isolation through containerd/runhcs, then reads back mode, image, and actual native identity. Its separately selected CNI/HCN adapter creates only the policy-bound HNS endpoint and records that endpoint ID in the same intent. `start` and `wait` use the bound task; `stop` is allowed only for the owner and current generation. `destroy` removes the exact task/compute identity and HNS endpoint, then checks both absent. Every operation returns a common envelope only after the native result passes validation. Uncertain results return `blocked` with reconciliation required; a retry must inspect the same attempt first.

Do not use a shell-concatenated command, an unbounded output buffer, a full container listing on each request, or a default runtime mode. Use typed runtime requests/argv, finite deadlines, bounded streams, and exact-ID lookup. HNS networking and writable scratch/layers are lifecycle resources whose cleanup must be journaled. The first fixture can use no inbound ports and a minimal outbound policy; SDN-compatible network policy IDs remain inputs to the adapter, not raw arbitrary HNS mutations.

The ordinary-client broker remains conditional on the selected privilege option. Its request carries authenticated caller, owner, image/command/mount/network allowlists, operation, and attempt generation. It rechecks all fields per mutation. Merely adding a user to a daemon named-pipe group is insufficient. The workload defaults to `ContainerUser`; a mount is admitted only after effective ACL inspection.

## Test and evidence gates

Use a source-matched Windows Server host and self-hosted Simple binary. Pure contract tests cover wrong OS, VM mode, stale generation, and malformed SDN. Windows integration tests cover the matrix (2025→2025 and 2025→2022, plus available same-version hosts), digest mismatch, actual process mode, a deliberate nonzero exit, bounded output, cancel/timeout, unauthorized second client, unmounted host-sentinel denial, mount ACLs, resource/network policy, and fresh exact-ID absence after destroy. If a pair is unavailable in the fixture, report it unqualified rather than a PASS.

A separate Windows 11 development fixture covers process-isolated Server 2022 and, where the installed build qualifies, Server 2025 images. Its evidence must show the explicit process request, observed process mode, and no utility VM; it does not establish production Windows Server support.

One primary SPipe manual should show prepare → create → start → wait → destroy, with failure scenarios folded and evidence paths for runtime mode, image digest/build, native ID, exit, and cleanup. Record warm startup, operation latency, and peak RSS; compare to selected NFRs when they exist. This Mac session can verify documentation and pure contract logic but cannot establish live Windows behavior.

See [architecture](../04_architecture/windows_server_process_container.md), [requirements](../02_requirements/feature/windows_server_process_container.md), and [system test plan](../03_plan/sys_test/windows_server_process_container.md).
