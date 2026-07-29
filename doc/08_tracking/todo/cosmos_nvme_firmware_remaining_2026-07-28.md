# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [bootstrap][P0] Run one bounded Retry 14 after the Retry 13 field-binding repair; only an admitted/deployed full CLI may execute the NVMe SSpec/docgen gate. Retry 13 used current pushed lifecycle authority `0c53d0bdcc80`, rebuilt the Rust authority, and stopped in Stage 2 after 24m43s on one deterministic error: expression-position `if val fld_base_sym = fld_base_sym_opt` lost its local and LLVM rejected the undeclared-global fallback. Peak RSS was 2,595,352 KiB with zero swap. Both optional `SymbolId` field paths now use the repository's proven `.?` plus `unwrap()` form, and the focused contract rejects the fragile bindings. Retry 11 remains the last Stage 4 evidence: it passed Stage 2/3 but failed after 1,278 surfaces with 10,292 OOB reads, 5,146 missing tags, `n_modules=0`, and missing streaming surfaces.
# DONE: [nvme][P0] Restore the RAM-NAND policy, linker regions, AXI endpoint/testbenches, GHDL runners, K26 NVMe/trace wiring, and SSpec/research artifacts deleted by consolidation. The recovery self-test and mocked AXI GHDL endpoint pass; source-matched full firmware GHDL remains behind Retry 13 admission.
# DONE: [nvme][P0] GHDL runs host-issued Create CQ/SQ, Identify, Write, Flush, and Read against `build/nvme_fw_rv32_service.elf`, retaining MMIO/DMA/IRQ/recovery/remap evidence.
# DONE: [nvme][P1] QEMU runs the same firmware command/recovery sequence through a GDB-driven guest-RAM mailbox; GHDL remains the AXI/DMA/IRQ authority.
# DONE: [cosmos][P1] Package manifest v3 binds a clean repository revision, compiler/linker/Bootgen identities, bound profile/contract, board serial/revision, boot mode, DMA bounds, and immutable artifact hashes; self-tests reject omissions and mismatches.
# DONE: [cosmos][P0] The board-campaign gate binds BT-001..BT-006 raw logs, campaign metadata, independent review, and the verified package by SHA-256; corruption fixtures fail closed.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006.

## Resume Order

1. Fix/admit the Stage-4 full CLI and run SSpec/docgen gates.
2. Pin the exact identified-board package and run BT-001..BT-006 on Cosmos+ hardware.
3. Run the optional UNO Q portability lane when its environment exists.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate.
