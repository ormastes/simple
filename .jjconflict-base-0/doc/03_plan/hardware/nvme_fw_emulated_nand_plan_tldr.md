# Emulated NAND plan (TL;DR)

> **Status (2026-06-29): E3 DONE.** The ONFI NAND device + FIL-as-driver is built and run-green
> as a SINGLE module `fw/fil_nand_device.spl` (a faithful drop-in for `fil_nand.Nand`), NOT the
> planned 4-module `nand_device`/`nand_bus`/`nand_bus_sw`/`nand_ctrl` split. Still future: E4
> async busy-timing reactor, full E5 no-alloc rv32 boot, E6 `nand_bus_mmio`. The rv32 direct-smoke
> path now boots and prints the firmware PASS marker, but it is not the full E5 port. Guide:
> `doc/07_guide/hardware/nvme_firmware/`.

Turn the in-process array NAND (`fil_nand`) into a real **emulated NAND device** behind an
**ONFI-style controller register seam**, so the FIL becomes a proper *driver* and the same
firmware runs on host, bare-metal rv32, and (later) a real/QEMU controller.

- **`NandDevice`** — the "chip": media + ONFI state machine (READ 00h/30h, PROGRAM 80h/10h,
  ERASE 60h/D0h, STATUS 70h, RESET FFh, ID 90h), STATUS/R/B#, busy timing (tR/tPROG/tBERS),
  fault + endurance + **power-fail** injection.
- **`NandBus`** seam — `reg_write/reg_read/buf_*` over a register map (CMD/ADDR/DATA/STATUS/RB/
  ECC_STATUS/DMA_*). Backends: `nand_bus_sw` (host + bare-metal) and `nand_bus_mmio` (future HW).
- **`nand_ctrl`** — DMA page transfer + ECC offload + IRQ/done over the bus.
- **`fil` rewrite** — issues ONFI sequences; **same public API → FTL/HIL unchanged** (the gate:
  `test_fw` + `sim_main` stay green). Media becomes async → the reactor polls R/B# with
  per-command deadlines (the coroutine payoff).
- **No-alloc** fixed-storage variant for bare-metal rv32 (`qemu-system-riscv32`), UART PASS.

Phases E1 device → E2 bus/ctrl → E3 fil swap (conformance) → E4 async timing → E5 rv32 boot →
E6 (stretch) mmio bus + QEMU controller. Parallel agents, Opus review per phase, `bin/simple run` gate.

Full plan: `nvme_fw_emulated_nand_plan.md`. Firmware: `examples/09_embedded/simpleos_nvme_fw/fw/`.

<!-- sdn-diagram:id=emu_nand_stack -->
```
FTL ─► FIL driver (ONFI sequences) ─► NandBus ─┬─ nand_bus_sw ─► NandDevice (host + rv32)
                                                └─ nand_bus_mmio ─► MMIO base (HW/QEMU, future)
                       nand_ctrl: DMA + ECC + IRQ over the bus
```
