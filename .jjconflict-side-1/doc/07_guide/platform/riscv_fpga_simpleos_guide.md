# SimpleOS on RISC-V FPGA — Overall Guide

Run SimpleOS in **minimal host mode** on a real RISC-V FPGA target: UART console, heap, trap vectors, basic scheduler, idle loop.

---

## Supported Boards

| Board | FPGA | CPU | Tool | Status |
|-------|------|-----|------|--------|
| **Kria K26** (primary) | Zynq UltraScale+ | VexRiscv-SMP (RV64GC) | Vivado 2025.2 | Primary target |
| **DE10-Nano** (secondary) | Cyclone V 5CSEBA6U23I7 | VexRiscv-SMP via LiteX | Quartus 26.1 | Secondary target |

Both boards use [VexRiscv-SMP](https://github.com/litex-hub/linux-on-litex-vexriscv) as the open-source RISC-V core, imported under `src/lib/hardware/opensource_rtl/vexriscv_smp/`.

---

## Build Pipeline Overview

```
[RTL Source]          [SimpleOS Kernel]
    |                       |
    v                       v
Synthesis             Cross-compile
(Vivado/Quartus)      (riscv64-unknown-elf-gcc)
    |                       |
    v                       v
Bitstream (.sof/.bit) SimpleOS ELF
    |                       |
    +----------+------------+
               |
               v
         Program FPGA
         Load ELF via JTAG
               |
               v
         Boot to UART console
```

### Detailed Steps

| Step | K26 | DE10-Nano |
|------|-----|-----------|
| RTL source | `src/lib/hardware/opensource_rtl/vexriscv_smp/` | Same (via LiteX) |
| SOC wiring | `src/lib/hardware/fpga_k26/k26_soc_top.spl` | LiteX auto-generated |
| Synthesis | Vivado 2025.2 (`build/build/xilinx_kv260/`) | Quartus 26.1 (LiteX) |
| Build script | `scripts/fpga/build_k26.shs` | `scripts/fpga/build_de10nano.shs` |
| Bitstream | `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` | `build/de10nano/gateware/de10nano.sof` |
| Program + load | `scripts/fpga/load_elf_k26.shs` | `scripts/fpga/load_elf_de10nano.shs` |
| Platform capsule | `src/os/kernel/arch/riscv64/platform/fpga.spl` | `src/os/kernel/arch/riscv64/platform/litex_fpga.spl` |
| Memory map | `src/os/kernel/arch/riscv64/platform/kria_memory_map.spl` | `src/os/kernel/arch/riscv64/platform/litex_memory_map.spl` |

---

## Memory Maps

### K26 (Kria / KriaFpgaMemoryMap)

| Region | Base Address | Size |
|--------|-------------|------|
| DRAM | `0x800000000` | 4 GB (PS DDR via AXI-HP0) |
| UART0 | `0xFF000000` | 4 KB |
| CLINT | `0xF8000000` | 64 KB |
| PLIC | `0xF9000000` | 4 MB |
| Heap start | Configured in `kria_memory_map.spl` | — |

Source: `src/os/kernel/arch/riscv64/platform/kria_memory_map.spl`

### DE10-Nano / LiteX (LitexFpgaMemoryMap)

| Region | Base Address | Size |
|--------|-------------|------|
| DRAM | `0x40000000` | 1 GB (DDR3 via LiteDRAM) |
| UART | `0xf0001000` | 4 KB |
| CLINT | `0xf0010000` | 64 KB |
| PLIC | `0xf0c00000` | 4 MB |
| Heap start | `0x40200000` | — |

Source: `src/os/kernel/arch/riscv64/platform/litex_memory_map.spl`

Both maps implement the `RiscvBoardMemoryMap` trait (`src/os/kernel/arch/riscv64/platform/board_memory_map.spl`).

---

## Quick Start: Kria K26

### Prerequisites
- Vivado 2025.2: `source ~/Xilinx/2025.2/settings64.sh`
- openFPGALoader: `sudo apt install openfpgaloader`
- Cross-compiler: `riscv64-unknown-elf-gcc`

### Build and Boot

```bash
# 1. Build bitstream (Vivado, ~20 min first time)
sh scripts/fpga/build_k26.shs

# 2. Build SimpleOS ELF for K26
bin/simple build --target=riscv64-fpga-kria

# 3. Program FPGA + load ELF (Vivado XSDB)
sh scripts/fpga/load_elf_k26.shs build/simpleos-kria.elf

# 4. Connect serial console (USB FT4232H)
picocom -b 115200 /dev/ttyUSB0
```

---

## Quick Start: DE10-Nano

### Prerequisites
- Quartus Prime Lite 26.1: see `de10nano_quartus_setup.md`
- LiteX: `pip install litex litex-boards`
- openFPGALoader: `sudo apt install openfpgaloader`

### Build and Boot

```bash
# 1. Build bitstream (LiteX + Quartus, ~15 min)
sh scripts/fpga/build_de10nano.shs

# 2. Build SimpleOS ELF for LiteX/DE10-Nano
bin/simple build --target=riscv64-fpga-litex

# 3. Program FPGA + load ELF (openocd + GDB)
sh scripts/fpga/load_elf_de10nano.shs build/simpleos-litex.elf

# 4. Connect serial console
picocom -b 115200 /dev/ttyUSB0
```

---

## Minimal Host Mode

SimpleOS boots in **minimal host mode** on FPGA — a constrained OS layer above bare-metal:

| Service | Status on FPGA |
|---------|---------------|
| M-mode entry + trap vectors | Required |
| S-mode handoff | Required |
| UART console | Required |
| Heap init | Required |
| Basic scheduler (idle loop) | Required |
| Full desktop / GUI | Not applicable |
| Network stack | Not applicable |

Boot sequence: `fpga_boot.spl` → M-mode setup → `riscv_noalloc_handoff.spl` → S-mode → `litex_fpga.spl` / `fpga.spl` platform init → scheduler idle loop.

---

## Troubleshooting

| Symptom | Likely Cause | Fix |
|---------|-------------|-----|
| No UART output after bitstream load | Wrong baud rate or port | Check `/dev/ttyUSB0` vs `ttyUSB1`; baud=115200 |
| Hang at M-mode entry | UART base address wrong for board | Verify `UART_BASE` in the active `*MemoryMap` capsule |
| `openFPGALoader: device not found` | USB-Blaster not detected (K26: FT4232H) | Check `lsusb`; udev rules; replug USB |
| ELF load hangs | XSDB/GDB lost connection | Power-cycle board; reprogram bitstream first |
| Heap corrupted at boot | Module-level `val` zeroed by BSS clear | Use function-local `val` with hex literals (see Known Constraints) |
| Quartus: "no device in JTAG chain" | Board not powered or MSEL wrong | See `de10nano_quartus_setup.md` troubleshooting |

---

## Related Files

| File | Purpose |
|------|---------|
| `doc/07_guide/platform/de10nano_quartus_setup.md` | DE10-Nano Quartus installation guide |
| `doc/09_bugs/riscv_fpga_port_bugs.md` | Bug tracking for this port |
| `src/lib/hardware/opensource_rtl/vexriscv_smp/mod.spl` | VexRiscv-SMP import manifest |
| `src/lib/hardware/fpga_k26/k26_soc_top.spl` | K26 SoC top wiring |
| `src/lib/hardware/fpga_k26/k26_axi_hp_bridge.spl` | AXI-HP bridge for K26 PS DDR |
| `src/os/kernel/arch/riscv64/platform/board_memory_map.spl` | `RiscvBoardMemoryMap` trait |
| `src/os/kernel/arch/riscv64/fpga_boot.spl` | M-mode entry point |
| `src/os/kernel/boot/riscv_noalloc_handoff.spl` | Boot handoff (M→S mode) |
| `scripts/fpga/build_k26.shs` | K26 Vivado build script |
| `scripts/fpga/build_de10nano.shs` | DE10-Nano LiteX build script |
| `scripts/fpga/load_elf_k26.shs` | K26 program + ELF load |
| `scripts/fpga/load_elf_de10nano.shs` | DE10-Nano program + ELF load |
