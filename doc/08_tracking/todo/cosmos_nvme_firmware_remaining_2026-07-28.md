# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [bootstrap][P0] First make one bounded Stage-2-only SSpec runner attempt using `--runtime-bundle core-c-bootstrap`, the corrected `stage2-runtime-authority`, `--mode one-binary`, and runner `--fork`; exact command and evidence are in `doc/08_tracking/bug/stage2_native_sspec_process_run_sigsegv_2026-07-29.md`. The broad runner build without that bundle failed in nine unrelated transitive modules after 52.72s; direct native-build of the NVMe spec succeeded in 10.85s but SIGSEGVed in `rt_process_run`/`memcpy`. If the bounded corrected recipe fails, resume only Stage 3 with one 90-minute cap; do not rerun a full bootstrap. Retry 15 already admitted Stage 2, fixed the Rust environment NUL panic, and reached a 45-minute Stage 3 cap with no further diagnostic. Retry 11 remains the last Stage 4 evidence: it passed Stage 2/3 but failed after 1,278 surfaces with 10,292 OOB reads, 5,146 missing tags, `n_modules=0`, and missing streaming surfaces.
# DONE: [nvme][P0] Restore the RAM-NAND policy, linker regions, AXI endpoint/testbenches, GHDL runners, K26 NVMe/trace wiring, SSpec/research artifacts, and the 609 deleted lines that implement `entry.spl` startup/queue/erase/program/read/prevention/recovery. The corrected Retry 15 Stage 2 pure-Simple compiler builds the restored 88,220-byte RV32 ELF in 17.56s at 158,580 KiB peak RSS.
# DONE: [nvme][P0] The source-matched Retry 15 Stage 2 image passes `check-rv32-nvme-nand-recovery.shs --ghdl`: behavioral soft-core, full AXI RAM, and clean plus garbage-filled synthesizable BRAM. The 89,668-byte ELF generated every ordered startup/queue/erase/program/read/prevention/recovery marker, performed 847 reads and 461 writes inside the exact 256-byte `.nandram`, and rejected word-64 access. Each 229-byte BRAM observation capture matched its own live UART stream. The current run retains its v1 source/ELF manifest; the hardened next-run gate binds the freshly built ELF explicitly, validates separate clean/garbage logs, and fail-closed records revision plus transitive source/evidence hashes in manifest v2.
# DONE: [nvme][P0] GHDL runs host-issued Create CQ/SQ, Identify, Write, Flush, and Read against `build/nvme_fw_rv32_service.elf`, retaining MMIO/DMA/IRQ/recovery/remap evidence.
# DONE: [nvme][P1] QEMU runs the same firmware command/recovery sequence through a GDB-driven guest-RAM mailbox; GHDL remains the AXI/DMA/IRQ authority.
# DONE: [cosmos][P1] Package manifest v3 binds a clean repository revision, compiler/linker/Bootgen identities, bound profile/contract, board serial/revision, boot mode, DMA bounds, and immutable artifact hashes; self-tests reject omissions and mismatches.
# DONE: [cosmos][P0] The board-campaign gate binds BT-001..BT-006 raw logs, campaign metadata, independent review, and the verified package by SHA-256; corruption fixtures fail closed.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006.

## Resume Order

1. Try the bounded Stage-2 runtime-bundle/fork SSpec runner and separate docgen.
2. Only if that fails, resume Stage 3 with the existing 90-minute cap.
3. Run the current SSpec/docgen gates.
4. Pin the exact identified-board package and run BT-001..BT-006 on Cosmos+ hardware.
5. Run the optional UNO Q portability lane when its environment exists.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate.
