# Agent tasks: UP Squared Apollo Lake Intel DCI debug

## Remaining implementation boundary (2026-08-22)

- Implement the executable resident UEFI mailbox adapter; the landed
  `dci_mailbox.spl` provides admission policy only.
- Add/admit the x86-64 PE32+ UEFI/MS-ABI target capsule and reviewed
  long-mode-to-Multiboot transition; the current GRUB child is too late to own
  UEFI page reservation, memory-map capture, or `ExitBootServices`.
- Prove CN16 RSP and NVMe Identify/provision/readback on physical UP2 hardware.
- Extend the physical/internal provisioner beyond the current format proof: bind
  all descendant mounts, swap, holders/slaves, dm/md/LVM relations, stable
  identity, exact image length/hash, flush, re-enumeration, and full readback.
- Keep direct DCI RAM boot blocked until mailbox publication, replay-safe load,
  final UEFI memory-map handoff, and entry transfer are executable and tested.

## Ownership

- Shared interfaces: `DciMailboxDescriptor`, `DciMemoryRange`,
  `DciLoadSegment`, `DciStorageIdentity`, `DciStorageWrite`, `DciAdmission`.
- Manual steps: “Admit the Intel DCI connection”, “Stage and commit the
  SimpleOS payload”, “Validate the physical ELF plan”, “Admit one storage
  write”, and “Retain physical boot/readback evidence”.
- Setup/checker helpers: `check-up-squared-apl-dci.shs` and
  `inspect-up-squared-apl-dci-elf.shs`.
- Parallel research lanes: primary-source Intel DCI/free-tool audit, UP2
  hardware/boot/storage audit, and repository completion audit. All were merged
  and reviewed by the primary agent without a higher-model override.
- Merge owner: primary Codex session.
- Final reviewer: primary normal-capability Codex verification pass.

## Sequence

1. Implement and unit-test pure mailbox/load/storage admission.
2. Add system scenario and manual mirror.
3. Integrate a UEFI resident adapter and prove it under OVMF.
4. Install CNDA-controlled Intel tooling after authenticated installer delivery.
5. Qualify physical connection, load/boot, UART/VFS, and storage readback.

No fail-fast placeholder is silently accepted. Hardware-only scenarios remain
explicitly BLOCKED until their real oracle is available.

## Current checkpoint (2026-08-22)

- Current kernel `31ce1fb4…e1fbdf` and USB image `983b74b9…b9ae8` pass the
  OVMF boot/VFS/RSP gate and the separate scratch-NVMe gate.
- Mailbox unit/system fixtures now match the current 225,152-byte ELF and its
  three inspected `PT_LOAD` records through `0x0b000000`.
- Pure-Simple executable spec/docgen verification remains blocked: the legacy
  v0.9.8 runner cannot parse current grammar, the admitted Stage-3 bootstrap is
  compile-only, and the current full CLI is not available. Do not use the Rust
  seed as release or SPipe evidence.
- Physical DCI, CN16, boot-menu/Secure-Boot, and physical storage evidence are
  still missing.
