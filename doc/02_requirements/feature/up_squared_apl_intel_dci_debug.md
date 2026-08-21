# Requirements: UP Squared Apollo Lake Intel DCI debug and provisioning

Date: 2026-08-21
Selection: Options A + B + D, confirmed by the user.

## Scope

The feature shall use Intel DCI for UP2 run control and RAM staging, retain the
proven UEFI path for first boot, add a resident target-side loader for repeated
RAM boot, and add identity-gated target-side storage provisioning. Raw
debugger-authored CPU-state boot and open xHCI DbC are excluded.

## Functional requirements

- **REQ-001 — Tool admission:** Installation shall accept only an authentic
  Intel System Debugger/System Bring-Up Toolkit installer obtained through the
  Intel CNDA/Registration Center flow. Absence is BLOCKED; no substitute package
  or repackaged binary is permitted.
- **REQ-002 — Cable admission:** A connection must enumerate an Apollo Lake
  target and CPU threads through Target Connection Agent. Smart KM Link,
  Tigard, an ordinary USB cable, or USB connector presence is not admission.
- **REQ-003 — Read-only first contact:** The first session shall prove target
  identity, halt/resume, registers, and a known physical-memory read before any
  RAM write. The retained receipt binds FAB, BIOS, tool, cable, and timestamp.
- **REQ-004 — Reset safety:** Apollo Lake OpenRC warm reset is forbidden.
  Physical reset is the baseline recovery. Power-Good reset remains blocked
  until independently proven on the exact board and firmware.
- **REQ-005 — DCI-assisted first boot:** UEFI/GRUB shall load the existing
  SimpleOS removable image while DCI supplies breakpoints and inspection.
- **REQ-006 — Resident mailbox:** A UEFI-loaded, target-side Simple component
  shall publish an allowlisted staging region and descriptor containing schema,
  generation, nonce, payload length, SHA-256, and commit state. Payload data is
  written before the descriptor is atomically committed.
- **REQ-007 — ELF admission:** The resident loader shall accept only the exact
  admitted x86-64 executable, validate bounds and non-overlap, copy every
  `PT_LOAD` from `p_offset` to `p_paddr`, and zero `p_memsz - p_filesz`.
- **REQ-008 — Boot transition:** Target-side code shall obtain the current UEFI
  memory map, exclude firmware/SMRAM/ACPI/MMIO/DMA-owned ranges, exit boot
  services, park application processors, and enter the reviewed Multiboot2
  32-bit shim. Direct contiguous ELF copy plus RIP assignment is forbidden.
- **REQ-009 — Storage provisioner:** A RAM-resident target-side driver shall
  enumerate storage and admit exactly one device by model, serial, transport,
  capacity, partitions, root/swap, mounts, holders, and explicit byte bounds.
  DCI controller-MMIO storage programming is forbidden.
- **REQ-010 — Write verification:** Provisioning shall require a device-identity
  and image-hash challenge, bounded write, flush, re-enumeration, and exact-length
  SHA-256 readback before PASS.
- **REQ-011 — Boot evidence:** Physical PASS requires one fresh CN16 transcript
  containing ordered loader, shim, entry, console, filesystem, and shell markers
  followed by command-correlated VFS-backed `ls /` results.
- **REQ-012 — Persistent mutation boundary:** No BIOS/SPI, MSR, UEFI-variable,
  internal eMMC/SATA, or removable-media mutation occurs without its separately
  admitted operation and explicit confirmation.

## Acceptance

Contract/OVMF evidence may prove implementation behavior but cannot satisfy
REQ-002, REQ-003, REQ-005 physical execution, REQ-010 physical readback, or
REQ-011. Those remain BLOCKED until the licensed Intel tool, qualified cable,
and exact board connection exist.

