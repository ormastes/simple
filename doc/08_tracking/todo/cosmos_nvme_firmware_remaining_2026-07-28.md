# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [bootstrap][P0] Bound Stage-4 full-CLI memory below the measured 64,552,584 KiB RSS peak, deploy it, then execute SSpec/docgen gates.
# TODO: [nvme][P0] Run host-issued admin/I/O queues against `build/nvme_fw_rv32_service.elf` in GHDL and retain MMIO/DMA/IRQ/recovery evidence.
# TODO: [nvme][P1] Run the same host sequence against the RV32 QEMU/RAM-NAND profile.
# TODO: [cosmos][P1] Complete package-manifest provenance for repository revision, dirty state, tool versions, bound profile, board identity, and immutable artifact hashes.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006.

## Resume Order

1. Complete the GHDL firmware-in-loop host sequence with the resident service ELF.
2. Fix/admit the Stage-4 full CLI and run SSpec/docgen gates.
3. Run QEMU parity for the same host sequence.
4. Complete package provenance and pin the exact board package.
5. Run the optional UNO Q portability lane when its environment exists.
6. Run BT-001..BT-006 only on the identified Cosmos+ board.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate.
