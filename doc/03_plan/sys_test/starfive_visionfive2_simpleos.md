<!-- codex-design -->
# StarFive VisionFive 2 SimpleOS system-test plan

## Contract scenario

Covers REQ-001/002/003/004/006/008 and NFR-001/003/006/007. Validate target/catalog/linker/entry/UART/root declarations, ELF receipt schema, RAM-only vocabulary, timeouts, and unchanged QEMU/FPGA contracts.

## Live scenario

Covers REQ-003/004/005/007/008/009 and NFR-001/002/004/005/006/008. Run one stateful sequence with the visible steps: Detect Tigard; Build StarFive image; Load image through U-Boot; Observe boot markers; Run ls on mounted root. Require adapter identity, DTB preservation, ordered markers, timings, VFS-backed entries, hashes, transcripts, and restored FTDI driver.

Hardware absence or silence is pending/BLOCKED, never PASS.

## Fail-closed self-test

Covers REQ-007/009 and NFR-001/002/006/008. Exercise missing/ambiguous USB, wrong serial/channel, all-ones/wrong TAP, UART silence, timeout, missing transcript, destructive JTAG without admitted TAP, and forbidden U-Boot flash verbs.

## Traceability

All REQ-001–009 and NFR-001–008 map to at least one scenario above. Offline contract checks do not substitute for the live scenario.
