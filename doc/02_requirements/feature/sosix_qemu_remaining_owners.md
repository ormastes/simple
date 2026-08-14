# SOSIX QEMU remaining-owner requirements

Status: selected by the canonical 24-row plan; implementation handoff active.

- `REQ-SOSIX-QEMU-L0-001`: The parent collector must report pending and must
  not report matrix promotion when any accepted row is non-PASS.
- `REQ-SOSIX-QEMU-L0-002`: Nonce-media preparation must reject source/run
  aliases, including aliases resolved before mutation.
- `REQ-SOSIX-QEMU-L0-003`: Filesystem compiler validation must execute only the
  row-admitted runtime identity.
- `REQ-SOSIX-QEMU-LINUX-OWNERS-001`: RV64, x86_32, and ARM32 remain fail-closed
  until their real compiler or privilege-lifecycle owners and live row bundles
  exist.
- `REQ-SOSIX-QEMU-EXTERNAL-001`: All 18 Windows, FreeBSD, and macOS acceptance
  IDs remain distinct, visible, and non-PASS until native producer evidence
  exists.
- `REQ-SOSIX-QEMU-HANDOFF-001`: Every incomplete owner has an exact resume
  command, canonical artifact root, owner, merge owner, and final reviewer.

The umbrella passes only when all 24 canonical bundles pass the collector.
