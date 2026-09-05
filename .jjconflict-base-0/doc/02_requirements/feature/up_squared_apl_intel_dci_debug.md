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
  SimpleOS removable image while a physically qualified DCI endpoint supplies
  only the run-control and inspection capabilities proven on this exact target.
- **REQ-006 — Resident mailbox:** A UEFI-loaded, target-side Simple component
  shall publish an allowlisted staging region and descriptor containing schema,
  generation, nonce, payload length, SHA-256, and commit state. Payload data is
  written before the descriptor is atomically committed.
- **REQ-007 — ELF admission:** The resident loader shall accept only the exact
  admitted x86-64 executable, validate bounds and non-overlap, copy every
  `PT_LOAD` from `p_offset` to `p_paddr`, and zero `p_memsz - p_filesz`.
- **REQ-008 — Boot transition:** Target-side code shall obtain the current UEFI
  memory map, exclude firmware/SMRAM/ACPI/MMIO/DMA-owned ranges, exit boot
  services, verify the firmware MP-services/topology contract, and enter the
  reviewed Multiboot2 32-bit shim. It shall not misuse `StartupAllAPs` as a
  permanent park operation; PI firmware owns the ExitBootServices AP-idle
  transition and the kernel owns later AP startup. Direct contiguous ELF copy
  plus RIP assignment is forbidden.
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
- **REQ-013 — Free post-boot RAM access:** After SimpleOS boots, a target-side
  GDB RSP monitor shall expose only a loader-reserved staging range over CN16.
  It shall checksum packets, cap each transfer, verify writes by readback, and
  return unsupported for registers, breakpoints, continue, step, or reset until
  real x86 trap-frame/run-control support exists.
- **REQ-014 — Firmware boot admission:** Physical removable boot shall record
  Secure Boot state and either use the F7 one-time entry or enter setup with
  DEL/ESC. An EFI-shell launch is a separate fallback and must identify the
  mapped filesystem and exact `EFI/BOOT/BOOTX64.EFI` artifact.

## Acceptance

Contract/OVMF evidence may prove implementation behavior but cannot satisfy
REQ-002, REQ-003, REQ-005 physical execution, REQ-010 physical readback, or
REQ-011. Those remain BLOCKED until the CNDA-controlled Intel tool,
Intel-qualified cable/probe, and exact board connection exist.
REQ-013 may pass under OVMF for protocol and RAM readback while physical CN16
transport remains a separate hardware evidence gate.

## Current implementation status (2026-08-22)

- REQ-001..005: documented/admitted gates; physical DCI remains BLOCKED because
  the CNDA-controlled toolkit, qualified cable/probe, enabled board, and
  connection receipt are absent.
- REQ-006..008: the executable GNU-EFI PE32+ publisher/consumer now reserves
  fixed mailbox, payload, shim, Multiboot-info, and kernel windows; enforces a
  nonce-bound commit-last wire-v1 descriptor; performs stable snapshots,
  SHA-256 and bounded ELF64 `PT_LOAD` admission; builds the final UEFI memory-map
  tag; retries `ExitBootServices` only on a stale key; and enters the embedded
  reviewed ELF32 shim through the x64-to-i386 trampoline. The
  `--ovmf-dci-admission` receipt proves an actual GDB-authored RAM payload boots
  SimpleOS without GRUB. Physical DCI transport and application-processor state
  on a multi-core UP2 remain open hardware gates, so REQ-008 is not yet
  a physical PASS.
- REQ-009..010: GPT/FAT32 proof and the new shared chunked raw-image owner are
  implemented. The latter binds DCI storage admission to live UP2 identity,
  hashes chunks before writes, maintains whole-image SHA-256, flushes, and
  performs exact fresh-adapter readback. The constant-memory streaming SHA fix
  passes the dedicated OVMF scratch-NVMe gate: target chunk hash, write, Flush,
  fresh-adapter exact readback, independent host SHA, and surrounding-range
  integrity all pass. Physical UP2 PCI/NVMe persistence remains BLOCKED.
- REQ-011: current-image OVMF UART evidence passes; physical CN16 evidence is
  missing.
- REQ-012: enforced by the current read-only boot and explicit challenges.
- REQ-013: current-image OVMF accepts four consecutive maximum `M` packets and
  exact `m` readback; physical CN16 remains BLOCKED.
- REQ-014: procedure is documented; physical Secure Boot/menu/shell evidence is
  missing.
- The current 256 MiB board image also boots as the only attached NVMe device
  under OVMF (`usb_attached=false`) and completes VFS-backed `ls /` without a
  media write. This is emulator boot-path evidence, not physical-board proof.
