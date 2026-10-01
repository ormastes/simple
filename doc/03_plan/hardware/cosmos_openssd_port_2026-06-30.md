# CRZ Cosmos+ OpenSSD — real NVMe-fw dev environment (config 3)

**Date:** 2026-06-30
**Target:** Xilinx Zynq-7000 XC7Z045, dual Cortex-A9 (ARMv7-A) — the CRZ Cosmos+ OpenSSD board.
**Status:** bring-up boots on the real Zynq emulation; silicon port gaps enumerated (impl-to-find).

The user's scope: "impl now to find missing part" (may not be testable on real silicon here). It
turned out to be *partially testable*: QEMU ships `xilinx-zynq-a9`, the actual Zynq-7000 machine.

## What runs today

`src/os/kernel/arch/arm32/cosmos/` is a Cortex-A9 bare-metal bring-up:
- `cosmos_start.S` — ARMv7 `_start`: CPU0 boots, secondary A9 cores park (MPIDR check), sets SP,
  calls `cosmos_boot_main`.
- `cosmos_uart.c` — Cadence UART driver (UART0 @0xE0000000, UART1 @0xE0001000): reset FIFOs, 8N1,
  enable TX, polled `rt_cadence_uart_put`. Prints the boot banner + the missing-parts list.
- `cosmos_linker.ld` — loads into DDR at 0x00100000 for `qemu-system-arm -M xilinx-zynq-a9 -kernel`.
- `build.shs` — `clang --target=armv7 -mcpu=cortex-a9` + `ld.lld`; `--run` boots it on qemu.

Verified: `sh src/os/kernel/arch/arm32/cosmos/build.shs --run` builds
`build/os/simpleos_cosmos_openssd.elf` and boots it on `xilinx-zynq-a9`, printing over the Cadence
UART:
```
COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK
[cosmos] Cadence UART1@0xE0001000 up; DDR/OCM mapped
[cosmos] NVMe-fw seams present: FMC register model (fil_fmc), HIL host queue
[cosmos] MISSING for silicon: Zynq NFC PL binding, PCIe endpoint, DDR/OCM init, A9 SMP/GIC, FSBL handoff
```
(Build the bring-up at `-O0` — QEMU's Cadence UART model is order-sensitive and `-O2` reordered the
volatile register writes.)

`src/os/kernel/arch/arm32/platform/cosmos_openssd.spl` is the firmware-facing descriptor: the
Zynq-7000 memory map + `cosmos_present_parts()` / `cosmos_missing_parts()` + a `cosmos_selftest`
that fails loudly while the port is incomplete (so the scaffold is never mistaken for done). Run:
`bin/simple run src/os/kernel/arch/arm32/platform/cosmos_openssd.spl`.

## Present firmware seams (reused unchanged from examples/09_embedded/simpleos_nvme_fw/)

These are MMIO-register / host-queue models, not toys — they map directly onto Cosmos+ hardware:
`fil_fmc` (FMC register driver, cf Cosmos+ `fmc_driver.c`), `fil_scheduler` (8ch×8way, cf
`low_level_scheduler.c`), `hil`/`hil_queue`/`hil_command` (NVMe host queues), `ftl`/`ftl_gc`/
`ftl_journal` (log-structured FTL + P2L recovery), `rain` (Lean-proven XOR parity),
`nvme_controller`/`nvme_admin`.

## Missing for a silicon (not-QEMU) port — the gap list

1. **Zynq NAND Flash Controller (PL IP @0x43C00000) MMIO binding** — wire `fil_fmc`'s abstract FMC
   registers to the real PL NFC. This is the single biggest gap (the firmware models it abstractly).
2. **PCIe endpoint init (PL IP @0x50000000)** — the NVMe-over-PCIe host transport. Zynq-7000 has no
   hard PCIe; Cosmos+ uses a PL PCIe IP.
3. **DDR controller + OCM init** — on hardware the FSBL does this via SLCR (0xF8000000); a bare-metal
   port must init the DDR3 controller.
4. **Cortex-A9 SMP + GIC bring-up** — release/park CPU1, GIC distributor (0xF8F01000) / CPU interface.
5. **MMU + L1/L2 (PL310) cache setup.**
6. **FSBL / BootROM handoff** — package as `boot.bin` (FSBL + bitstream + this ELF) for real silicon.
7. **ARMv7 freestanding Simple runtime** — the `rt_*` runtime for armv7 baremetal. rv32/rv64 share
   `freestanding_runtime.c`; arm needs the equivalent so the *Simple* firmware (not just the C
   bring-up) can run on the A9. This is the prerequisite to porting the FTL/HIL onto the board.

## Next step

The ARMv7 freestanding runtime (#7) unblocks running the actual Simple firmware on the A9; then the
NFC binding (#1) connects `fil_fmc` to silicon. The C bring-up here proves the board/UART/boot path.
