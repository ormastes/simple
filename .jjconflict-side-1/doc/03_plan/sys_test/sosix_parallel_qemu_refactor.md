# SOSIX Multi-Host QEMU System-Test Plan

## Traceability

| Requirement | Executable evidence |
|---|---|
| REQ-SQ-001,009,011 | settings contract/unit spec and matrix wrapper self-test |
| REQ-SQ-002,010 | SOSIX core/FS unit and POSIX integration specs |
| REQ-SQ-003,004 | host × guest matrix scenario |
| REQ-SQ-005 | per-ISA boot marker and serial identity |
| REQ-SQ-006 | in-guest filesystem listing transcript |
| REQ-SQ-007 | arbitrary filesystem program stdout + rc |
| REQ-SQ-008 | target-native Simple version and hello compile/run transcript |
| REQ-SQ-012 | blocked-row resume record and fail-closed aggregate |
| REQ-SQ-013 | storage resolver precedence/self-test and current-host receipt |
| REQ-SQ-014,015 | WM host-service adapter unit/integration tests plus native/headless/QEMU production-path evidence |

## Scenario contract

Executable specs stay under `test/03_system/os/qemu/`; generated manuals stay under `doc/06_spec/03_system/os/qemu/`. A matrix row cannot pass from source inspection, file existence, host-side commands, cached transcripts with mismatched argv/hash, or fixed SSH/QEMU responses.

The aggregate passes only when every required cell has a current evidence bundle and every bundle proves all six operator steps. Unavailable hosts are represented as blocked scenarios and keep the aggregate red.

The shared pure classifier is `src/os/sosix/qemu_evidence/guest_filesystem_receipt.spl`; its contract spec is `test/01_unit/os/sosix/qemu_guest_filesystem_receipt_spec.spl`. It cannot promote a row by itself: system lanes must populate the receipt from retained production-guest transcripts.

Guest producers emit exact nonce-correlated `SOSIX_QEMU_BOOT`, `SOSIX_QEMU_FS_MOUNT`, `SOSIX_QEMU_FS_LS`, and `SOSIX_QEMU_PROGRAM` markers. Host, guest, and nonce must match across every marker. The parser rejects replay across nonces and an explicit fixed-response marker.

## Required sabotage

- Change descriptor hash: stale bundle rejected.
- Remove executed accelerator: native classification rejected.
- Remove boot marker: boot row fails.
- Remove `firmware_identity` or `firmware_mode`: descriptor/evidence admission fails before a serial transcript can receive credit.
- Replace `ls` output with host output: provenance check fails.
- Replace arbitrary program with fixed response: nonce/source/output correlation fails.
- Make program return nonzero: execution row fails.
