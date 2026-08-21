# Agent tasks: UP Squared Apollo Lake Intel DCI debug

## Ownership

- Shared interfaces: `DciMailboxDescriptor`, `DciMemoryRange`,
  `DciLoadSegment`, `DciStorageIdentity`, `DciStorageWrite`, `DciAdmission`.
- Manual steps: “Admit the Intel DCI connection”, “Stage and commit the
  SimpleOS payload”, “Validate the physical ELF plan”, “Admit one storage
  write”, and “Retain physical boot/readback evidence”.
- Setup/checker helpers: `check-up-squared-apl-dci.shs` and
  `inspect-up-squared-apl-dci-elf.shs`.
- Lower-model sidecar lanes: N/A; the user prohibited higher-model substitution
  and did not request parallel agents.
- Merge owner: primary Codex session.
- Final reviewer: primary normal-capability Codex verification pass.

## Sequence

1. Implement and unit-test pure mailbox/load/storage admission.
2. Add system scenario and manual mirror.
3. Integrate a UEFI resident adapter and prove it under OVMF.
4. Install licensed Intel tooling after authenticated installer delivery.
5. Qualify physical connection, load/boot, UART/VFS, and storage readback.

No fail-fast placeholder is silently accepted. Hardware-only scenarios remain
explicitly BLOCKED until their real oracle is available.

