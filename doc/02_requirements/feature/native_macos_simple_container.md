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

## Seatbelt lane: portable policy profile (SC-MAC, 2026-11-13)

The direct-Seatbelt lane (`macos-seatbelt-process`, design
`doc/05_design/simple_container_macos_seatbelt.md`) is separate from the
signed-App-Sandbox requirements above, which are unchanged. Its portable
policy layer is implemented in pure Simple and runs on any host:

- Schemas `simple-container-seatbelt-policy-v1` and `simple-endpoint-network-v1`
  (`src/lib/common/container_policy/*_schema.sdn`), strict-decoded with the
  canonical SDN parser and source spans (SC-MAC-017).
- Separate read-data / read-metadata / write / execute / IPC grants with
  explicit recursive scope, and deterministic grant/deny overlap refusal over
  resolved host facts (SC-MAC-005, SC-MAC-006).
- Evidence profiles `strict-owned-attempt-v1` and `finite-parent-owned-v1`;
  admission refuses `pod-ip-v1`, unenforceable hard limits and unobserved
  strict descendant absence before any effect (SC-MAC-011, -014, -018).

Every host without recorded native evidence reports `Unqualified`, so
admission is blocked (SCMAC-PLATFORM-001). Real macOS qualification of
enforcement remains open; no requirement here is satisfied by these models.
The direct-Seatbelt lane (`macos-seatbelt-process-v1`) is a separate profile
with its own requirement IDs SC-MAC-001..024 in
[simple_container_macos_seatbelt](../../05_design/simple_container_macos_seatbelt.md);
it does not rewrite REQ-NMC-001..005. Its profile emitter, qualification model
and fail-closed provider exist in source; no SC-MAC requirement that needs a
native macOS receipt is satisfied yet.
