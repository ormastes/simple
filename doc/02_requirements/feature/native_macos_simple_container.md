# Native macOS and SimpleOS Simple Container requirements

Selected by the user's 2026-09-27 correction: Simple Container is not a VM.
Mac programs run on the Mac host; SimpleOS programs run on SimpleOS. The two
providers share common identity, lifecycle, admission, and receipt values.

| ID | Requirement | Acceptance |
|---|---|---|
| REQ-NMC-001 | Admit only `macos/macos/native-sandbox` for the Mac route. | Reject a VM, Linux image, SimpleOS image, or cross-OS native tuple. |
| REQ-NMC-002 | Use a signed macOS App Sandbox helper and signed inheriting workload with owned native process observation. | Verify helper/child entitlements and actual sandbox status; bind PID/start identity to the attempt. |
| REQ-NMC-003 | Publish a Mac exit only from the bound native process and then prove cleanup. | Exercise chosen nonzero exit, timeout/cancel, wrong identity, filesystem denial, bounded output, and fresh absence. |
| REQ-NMC-004 | Keep SimpleOS execution within its own kernel container provider. | A SimpleOS scheduler task and kernel-origin exit, with authenticated loader authority, pass on SimpleOS. |
| REQ-NMC-005 | Share the `RuntimeIdentityV1`/`RuntimeOperationV1` contract and SDN capability receipt. | Both providers pass exact host/execution-OS admission; native handles remain provider-owned. |

Mac App Sandbox is a `native-sandbox` capability, not a claim of Linux/Windows
kernel container isolation. Do not admit unrelated concurrent tenants through
one shared App Sandbox identity without separate isolation evidence.
