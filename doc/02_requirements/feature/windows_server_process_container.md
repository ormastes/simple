# Windows Server process-isolated Simple Container requirements

The user selected real Windows process containers sharing the Windows Server
kernel. Hyper-V isolation and all VM routes are excluded. Client privilege
policy remains a separate selection in
[cross-host options](simple_container_cross_host_options.md).

| ID | Requirement | Acceptance |
|---|---|---|
| REQ-WPC-001 | Admit only `windows/windows/native-container` with process isolation. | Reject Hyper-V, VM, HostProcess, Linux images, and cross-OS tuples before create; verify observed mode after create. |
| REQ-WPC-002 | Use a compatible immutable Windows image and native HCS-backed runtime. | Record host/image build, digest, provider ID, and actual compute identity; admit only pairs in the current Microsoft process-isolation matrix. |
| REQ-WPC-003 | Bind create/start/wait/stop/destroy to one attempt and native compute-system identity. | Chosen nonzero exit, bounded output, cancellation, and exact-ID absence pass on Windows Server. |
| REQ-WPC-004 | Enforce the selected ordinary-client authority policy. | Unauthorized second client cannot create, inspect, stop, or destroy another attempt. |
| REQ-WPC-005 | Share the common lifecycle and SDN receipt with other Simple Container providers. | HCS handles stay in the Windows leaf; copied receipt never authorizes mutation. |

Process isolation is not the strongest boundary for hostile multitenant code;
the admission policy must disclose that limitation rather than switching to a
VM. Source-matched live Windows evidence is required before support is claimed.
