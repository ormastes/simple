# SimpleOS Filesystem Servers QEMU Contract

Source: `test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl`

Evidence class: `source-contract`. This specification validates the production
QEMU gate; it does not itself claim a live guest pass.

## Scenarios

- Reject kernel-resident or partial evidence and require x86_64, ARM64, and
  RISC-V 64 guest receipts.
- Require HTTP bytes loaded from the guest filesystem, a committed DB write
  surviving reboot, and hashes binding artifacts and transcripts.
- Reject aliased evidence files so one receipt cannot impersonate several
  architecture runs.

Production gate: `scripts/check/check-simpleos-filesystem-servers-qemu.shs`.

