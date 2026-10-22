# Windows Server process-isolated Simple Container plan

Selected isolation: native Windows process container on Windows Server. No
Hyper-V, guest VM, or Linux image fallback. Client privilege selection is
still pending; a non-admin daily client requires a scoped delegated service
unless a genuine user-level native path is demonstrated.
Recommendation: choose F2 in the cross-host privilege options for a non-admin
daily client; a privileged, per-operation broker is the only currently
plausible native Windows route, pending live authorization proof. F1 accurately
reports Windows launch unavailable; F3 requires an Administrator client and a
capability contract revision. This recommendation does not select F2 for the
user.

Merge owner: Codex. Windows provider owner: dedicated Windows host lane.
Final reviewer: Astra or equivalent. Sidecars: N/A until the HCS adapter
interface is fixed.

1. Freeze the `windows/windows/native-container` request and provider ID
   `windows-process-container-v1`. Probe Server edition/build, Containers
   feature, containerd/runhcs/HCS, compatible image, and current caller
   authorization separately. Do not require Hyper-V role.
2. Implement a Windows leaf over containerd → the available runhcs V1 shim →
   HCS. Containerd/shim owns native handles; the Simple leaf owns its client
   connection, journal, generation, copied native IDs, and result validation.
   The process-specific V2 shim is documented as coming soon and is not a
   dependency. Containerd is community-supported on Windows Server; record
   that runtime-support choice separately from OS support. Select an explicit
   CNI/HCN adapter for HNS endpoint create/destroy rather than assuming task
   creation provisions networking. Convert observed operations to the shared
   `RuntimeIdentityV1` and `RuntimeOperationV1` envelopes.
3. Pin an immutable Windows image. Check the Microsoft host/image version
   matrix, including the Server 2025 → Server 2022 exception, without assuming
   all patch revisions must match. Require and observe process isolation;
   record independent evidence that the task has no utility VM, and reject VM
   and HostProcess modes. Start as `ContainerUser` and explicitly authorize
   mount ACLs and SDN-compatible HNS network policy.
4. Under the selected privilege policy, prove one ordinary client can manage
   only its own allowlisted workload. Test a second identity's create,
   inspect, stop, and destroy denial. Do not equate Docker named-pipe access
   with operation-scoped authorization.
5. On Windows Server, run source-matched Simple contract/system specs and a
   live fixture with chosen nonzero exit, bounded output, timeout, cancel,
   stale identity, wrong image/build, incompatible mode, and fresh exact-ID
   absence after destroy. Store bounded SDN receipts and measured latency/RSS.
6. In a separate developer lane, probe Windows 11 process isolation with a
   Server 2022 image and, on a compatible 24H2-or-later host, a Server 2025
   image. Require an explicit process-mode request and actual-mode evidence;
   keep this preview result separate from production Windows Server support.

See [Windows TODO](../../08_tracking/todo/simple_container_windows_server_qualification_2026-09-27.md)
and [Windows architecture](../../04_architecture/windows_server_process_container.md),
[detail design](../../05_design/windows_server_process_container.md), and
[domain research](../../01_research/domain/windows_server_process_container.md).
