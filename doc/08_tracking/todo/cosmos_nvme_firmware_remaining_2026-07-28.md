# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [bootstrap][P0] Bound Stage-4 full-CLI memory below the measured 64,552,584 KiB RSS peak, deploy it, then execute SSpec/docgen gates.
# DONE: [nvme][P0] GHDL runs host-issued Create CQ/SQ, Identify, Write, Flush, and Read against `build/nvme_fw_rv32_service.elf`, retaining MMIO/DMA/IRQ/recovery/remap evidence.
# DONE: [nvme][P1] QEMU runs the same firmware command/recovery sequence through a GDB-driven guest-RAM mailbox; GHDL remains the AXI/DMA/IRQ authority.
# DONE: [cosmos][P1] Package manifest v3 binds a clean repository revision, compiler/linker/Bootgen identities, bound profile/contract, board serial/revision, boot mode, DMA bounds, and immutable artifact hashes; self-tests reject omissions and mismatches.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006.

## Resume Order

1. Fix/admit the Stage-4 full CLI and run SSpec/docgen gates.
2. Pin the exact identified-board package and run BT-001..BT-006 on Cosmos+ hardware.
3. Run the optional UNO Q portability lane when its environment exists.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate.
