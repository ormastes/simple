# Cosmos NVMe Firmware Remaining Work

These items are deliberately separate from completed host/ARM contract work.
Postponed hardware rows remain open and must not be converted into host PASS.

# TODO: [bootstrap][P0] Resume only Stage 3 with one 90-minute bound from the corrected Retry 15 Stage 2 authority; do not rerun a full bootstrap. Retry 15 used pushed authority `bf492d318cf6`: Stage 2 passed and produced an admitted pure-Simple `simple-bootstrap` binary, but the NVMe post-bootstrap gate proved that this intentionally minimal CLI cannot execute `run`/`test`. The first Stage 3-only resume aborted after 5m30s because Rust `rt_env_set` passed an embedded NUL to `std::env::set_var`. The runtime boundary now rejects NUL/invalid keys and its focused Rust regression passes. Targeted runtime archives rebuilt in 4m19s (2,593,232 KiB peak), corrected Stage 2 rebuilt from cache in 1m32s (949,080 KiB peak), and the corrected Stage 3 run cleared the crash but reached its 45m cap CPU-active with no diagnostic or final artifact (1,567,392 KiB peak). A full CLI relink remains necessary only after Stage 3 because Stage 2/3 are bootstrap-only; that full CLI then runs the canonical NVMe SSpec/docgen/GHDL wrapper. Retry 11 remains the last Stage 4 evidence: it passed Stage 2/3 but failed after 1,278 surfaces with 10,292 OOB reads, 5,146 missing tags, `n_modules=0`, and missing streaming surfaces.
# DONE: [nvme][P0] Restore the RAM-NAND policy, linker regions, AXI endpoint/testbenches, GHDL runners, K26 NVMe/trace wiring, SSpec/research artifacts, and the 609 deleted lines that implement `entry.spl` startup/queue/erase/program/read/prevention/recovery. The corrected Retry 15 Stage 2 pure-Simple compiler builds the restored 88,220-byte RV32 ELF in 17.56s at 158,580 KiB peak RSS.
# DONE: [nvme][P0] The source-matched Retry 15 Stage 2 image passes `check-rv32-nvme-nand-recovery.shs --ghdl`: behavioral soft-core, full AXI RAM, and clean plus garbage-filled synthesizable BRAM. The 89,668-byte ELF generated every ordered startup/queue/erase/program/read/prevention/recovery marker, performed 847 reads and 461 writes inside the exact 256-byte `.nandram`, and rejected word-64 access. Each 229-byte BRAM observation capture matched its own live UART stream. The current run retains its v1 source/ELF manifest; the hardened next-run gate binds the freshly built ELF explicitly, validates separate clean/garbage logs, and fail-closed records revision plus transitive source/evidence hashes in manifest v2.
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
