# Windows Server process-container system test plan

| Requirement | Live Windows Server check |
|---|---|
| REQ-WPC-001 | Native process isolation requested and observed; Hyper-V, HostProcess, and cross-OS requests rejected before HCS create. |
| REQ-WPC-002 | Compatible pinned Windows image starts; 2025→2022 is accepted where qualified; wrong build/digest fails closed. |
| REQ-WPC-003 | Exact compute ID binds create/start/wait/stop/destroy; nonzero exit, bounded output, timeout, and fresh absence verified. |
| REQ-WPC-004 | Ordinary client policy and second-client denial tested under the selected privilege option. |
| REQ-WPC-005 | Shared SDN receipt validates identity and phase; stale generation/replayed receipt cannot mutate native state. |

Run focused Simple specs on a source-matched Windows binary and preserve the
HCS/containerd event and cleanup evidence. No Windows host is attached to this
session, so these are planned scenarios, not PASS results.
