# System test plan: UP Squared Apollo Lake Intel DCI debug

## Executable specification

`test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl`

## Requirement mapping

- REQ-001/002/003: source and receipt gate rejects missing/non-DCI tooling.
- REQ-004: contract rejects OpenRC warm reset.
- REQ-005/011: existing OVMF and live UART oracle retain distinct verdicts.
- REQ-006: committed fresh mailbox passes; partial/replayed/hash-mismatched
  descriptors fail.
- REQ-007/008: exact UP2 segment shape passes; truncated, overlapping,
  out-of-range, W+X, and non-executable-entry plans fail.
- REQ-009/010/012: exact storage identity/challenge passes policy; system,
  mounted, held, mismatched, overflowed, and unconfirmed writes fail.
  The common image scenario additionally proves ordered chunk hashes,
  whole-image digest, flush, and exact fresh-view readback on an isolated block
  device. `--ovmf-image-provision` repeats this through the NVMe adapter and
  retains independent host SHA plus unchanged surrounding-range evidence;
  physical persistence remains a separate receipt.
- REQ-013: OVMF enters the serial RSP monitor, writes `SIMP` with `M`, reads
  `53494d50` with `m`, detaches, and observes the resumed shell. Unit scenarios
  reject malformed checksums, overflow, out-of-range memory, and false run
  control.
- REQ-014: physical evidence records Secure Boot state and distinguishes F7
  one-time boot, DEL/ESC setup, and any EFI-shell fallback. No emulator-only
  assertion promotes this physical requirement to PASS.

## Evidence levels

The executable spec proves pure policy only. The existing OVMF oracle proves
firmware boot semantics. Physical DCI, boot, and storage scenarios remain
visible as BLOCKED until their retained receipts exist; they are never skipped
or counted as PASS.
The current-image OVMF oracle additionally proves RSP RAM write/readback within
the reserved ELF segment; it does not prove physical CN16 wiring.
The NVMe-only OVMF oracle boots the current 256 MiB image with no USB device and
requires VFS-backed `ls /`; it does not prove the physical UP2 boot menu or SSD.
The `--ovmf-dci-admission` oracle starts OVMF halted at reset, uses GNU GDB's
remote memory transport to continue into the resident PE32+ loader, preserves
the published nonce, writes the exact current SimpleOS ELF and raw digest, and
commits the aligned word last. It requires admission, the embedded ELF32 shim,
`_entry32`, kernel, filesystem, and shell markers without GRUB fallback. This
proves REQ-006/007 and the single-CPU software portion of REQ-008; physical DCI
and UP2 firmware/kernel application-processor state remain separate evidence.
The paired `--ovmf-dci-rejection` oracle publishes the same complete kernel with
an all-zero descriptor digest and requires `blocked=payload-sha256` with no
admission, transition, or GRUB fallback.
The `--image-reproducibility` oracle builds twice concurrently into fresh
directories at epoch `1704067200`, requires byte-identical GPT/FAT32 images and
stable ESP/PE/GRUB/shim components, and retains the common SHA-256. The normal
structural checker separately requires the pinned disk GUID, ESP GUID, FAT
serial, and boot contracts. The gate also binds the executable DCI policy
fixture's kernel hash and byte length to the admitted kernel receipt.
