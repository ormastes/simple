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
- REQ-013: OVMF enters the serial RSP monitor, writes `SIMP` with `M`, reads
  `53494d50` with `m`, detaches, and observes the resumed shell. Unit scenarios
  reject malformed checksums, overflow, out-of-range memory, and false run
  control.

## Evidence levels

The executable spec proves pure policy only. The existing OVMF oracle proves
firmware boot semantics. Physical DCI, boot, and storage scenarios remain
visible as BLOCKED until their retained receipts exist; they are never skipped
or counted as PASS.
The OVMF oracle additionally proves RSP RAM write/readback within the reserved
ELF segment; it does not prove physical CN16 wiring.
