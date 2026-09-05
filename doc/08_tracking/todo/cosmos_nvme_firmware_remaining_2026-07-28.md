# Cosmos NVMe Firmware Completion Status

The user-approved completion boundary is KV260/K26 emulation. Physical Cosmos+
and UNO Q campaigns are postponed because the required hardware is unavailable;
they remain future hardware qualification and must not be converted into host
or GHDL PASS.

# DONE: [bootstrap][P0] Admit the user-approved Phase 2 compiler/test path containing the fixed process-runtime ABI and native docgen lowering. A current-source Stage 2 linked with the rebuilt LLVM native-all authority emits `(cmd_ptr, cmd_len, args)`, and its exact native NVMe SSpec passed 5 examples with 0 failures, including clean/garbage GHDL and AXI prevention/recovery. The same artifact compiled standalone docgen, which parsed all five scenarios with zero stubs. The global deployed full CLI remains stale and is not this evidence. No additional Stage 3 run or full bootstrap was required; exact hashes and logs are recorded in `doc/08_tracking/bug/stage2_native_sspec_process_run_sigsegv_2026-07-29.md`.
# DONE: [nvme][P0] Restore the RAM-NAND policy, linker regions, AXI endpoint/testbenches, GHDL runners, K26 NVMe/trace wiring, SSpec/research artifacts, and the 609 deleted lines that implement `entry.spl` startup/queue/erase/program/read/prevention/recovery. The corrected Retry 15 Stage 2 pure-Simple compiler builds the restored 88,220-byte RV32 ELF in 17.56s at 158,580 KiB peak RSS.
# DONE: [nvme][P0] The source-matched Retry 15 Stage 2 image passes `check-rv32-nvme-nand-recovery.shs --ghdl`: behavioral soft-core, full AXI RAM, and clean plus garbage-filled synthesizable BRAM. The 89,668-byte ELF generated every ordered startup/queue/erase/program/read/prevention/recovery marker, performed 847 reads and 461 writes inside the exact 256-byte `.nandram`, and rejected word-64 access. Each 229-byte BRAM observation capture matched its own live UART stream. The current run retains its v1 source/ELF manifest; the hardened next-run gate binds the freshly built ELF explicitly, validates separate clean/garbage logs, and fail-closed records revision plus transitive source/evidence hashes in manifest v2.
# DONE: [nvme][P0] GHDL runs host-issued Create CQ/SQ, Identify, Write, Flush, and Read against `build/nvme_fw_rv32_service.elf`, retaining MMIO/DMA/IRQ/recovery/remap evidence.
# DONE: [nvme][P1] QEMU runs the same firmware command/recovery sequence through a GDB-driven guest-RAM mailbox; GHDL remains the AXI/DMA/IRQ authority.
# DONE: [cosmos][P1] Package manifest v3 binds a clean repository revision, compiler/linker/Bootgen identities, bound profile/contract, board serial/revision, boot mode, DMA bounds, and immutable artifact hashes; self-tests reject omissions and mismatches.
# DONE: [cosmos][P0] The board-campaign gate binds BT-001..BT-006 raw logs, campaign metadata, independent review, and the verified package by SHA-256; corruption fixtures fail closed.
# DONE: [nvme][P0] Complete the available KV260/K26 emulation scope. The retained GHDL run drives the synthesizable K26 top and its AXI4 RAM NAND window under garbage-filled DDR, reaches the terminal marker, records 847 NAND-window reads and 461 writes, and emits the ordered startup, admin queue, I/O queue, erase, program, read, prevention, and recovery PASS markers. The exact native SSpec passed 5 examples with 0 failures and standalone docgen parsed all 5 scenarios with 0 stubs.
# TODO: [uno_q][P2] POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance.
# TODO: [cosmos][P0] POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured.

## Future Hardware Qualification

1. Pin the exact identified-board package and run BT-001..BT-006 on Cosmos+ hardware.
2. Run the optional UNO Q portability lane when its environment exists.

The canonical wrapper is
`scripts/check/check-nvme-firmware-remaining-gates.shs`. Its host result and
external-board result are intentionally separate. These postponed campaigns do
not block completion of the KV260/K26 emulation scope.
