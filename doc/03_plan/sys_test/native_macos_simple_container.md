# Native macOS Simple Container test plan

Use the self-hosted Simple runtime. No QEMU, Docker, or VM fixture counts.

| Requirement | Test evidence |
|---|---|
| REQ-NMC-001 | Pure admission accepts macos/macos/native-sandbox and rejects VM/cross-OS tuples. |
| REQ-NMC-002 | A signed helper with the expected entitlements launches a pinned macOS program; a missing/changed signature fails before launch. |
| REQ-NMC-003 | Live Mac workload returns a chosen nonzero native exit; host sentinel access is denied; timeout/cancel and a child attempting to detach leave fresh absence or block provider admission. |
| REQ-NMC-004 | A SimpleOS-native fixture launches through authenticated loader authority and observes kernel task exit on SimpleOS. |
| REQ-NMC-005 | Both providers use the same copied runtime identity/operation and bounded SDN receipt while retaining their native handles locally. |

The current pure admission and SDN specs cover part of REQ-NMC-001/005 in
source only. Remaining executable specs are blocked until the provider/helper
and source-matched Simple runtime exist. Do not add placeholder PASS tests.
