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
- Require verified target credential zeroization for every architecture and
  bind the first- and second-boot zeroization receipts by nonzero SHA-256.
- Reject residual credential bytes, uncleared digest workspaces, unverified
  target cleanup, and host-only destruction of a credential-bearing image.
- Wire the production payload producer for x86_64, ARM64, and RISC-V 64 target
  triples, require no-stub compilation, reject unresolved strong symbols, and
  validate the staged ELF machine before image admission. This scenario reads
  the wiring; it does not invoke or prove a payload build.
- Keep the x86_64 and RISC-V 64 filesystem-server boot entries on their
  architecture scheduler/VFS owners and require explicit QEMU failure exits
  when authenticated `/SERVERS.ELF` launch cannot complete.

Production gate: `scripts/check/check-simpleos-filesystem-servers-qemu.shs`.
