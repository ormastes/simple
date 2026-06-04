# DE10-Nano Quartus Prime Setup Guide

> Secondary FPGA target: Terasic DE10-Nano (Cyclone V 5CSEBA6U23I7)
> Primary target is Kria K26 — see `riscv_fpga_simpleos_guide.md`.

## Prerequisites

| Requirement | Details |
|-------------|---------|
| Host OS | Ubuntu 22.04+ (or Debian 12+) |
| Disk space | ~30 GB free (Quartus installer ~8 GB, installed ~22 GB) |
| RAM | 8 GB minimum, 16 GB recommended |
| USB | USB-Blaster II (built into DE10-Nano) |
| Python | 3.10+ (for LiteX) |

---

## 1. Download Quartus Prime Lite 26.1

Quartus Prime **Lite Edition** is free — no license needed for Cyclone V.

1. Go to: https://www.intel.com/content/www/us/en/collections/products/fpga/software/downloads.html
2. Select: **Quartus Prime Lite Edition 26.1** → Linux
3. Download components:
   - `QuartusLiteSetup-26.1.x.x-linux.run` (~4.5 GB)
   - `CycloneVSetup-26.1.x.x-linux.run` (device support, ~1.5 GB)

---

## 2. Install Quartus

```bash
# Make executables
chmod +x QuartusLiteSetup-26.1.*.run CycloneVSetup-26.1.*.run

# Run installer (GUI or --mode unattended)
./QuartusLiteSetup-26.1.*.run --mode unattended --installdir ~/intelFPGA_lite/26.1

# Device support (run after Quartus installs)
./CycloneVSetup-26.1.*.run --mode unattended --installdir ~/intelFPGA_lite/26.1
```

Add to PATH (append to `~/.bashrc` or `~/.profile`):

```bash
export QUARTUS_ROOTDIR=~/intelFPGA_lite/26.1/quartus
export PATH=$QUARTUS_ROOTDIR/bin:$PATH
```

Verify:
```bash
quartus_sh --version
# Expected: Quartus Prime Shell Version 26.1 ...
```

---

## 3. USB-Blaster Udev Rules

Without udev rules, Quartus Programmer cannot access the USB-Blaster without root.

```bash
# Create udev rule
sudo tee /etc/udev/rules.d/51-usbblaster.rules <<'EOF'
# Intel USB-Blaster / USB-Blaster II
SUBSYSTEM=="usb", ATTRS{idVendor}=="09fb", ATTRS{idProduct}=="6001", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="09fb", ATTRS{idProduct}=="6002", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="09fb", ATTRS{idProduct}=="6003", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="09fb", ATTRS{idProduct}=="6010", MODE="0666"
SUBSYSTEM=="usb", ATTRS{idVendor}=="09fb", ATTRS{idProduct}=="6810", MODE="0666"
EOF

sudo udevadm control --reload-rules && sudo udevadm trigger
```

Reconnect the DE10-Nano USB cable after applying rules.

---

## 4. LiteX Environment Setup

LiteX generates the VexRiscv-SMP SoC for the DE10-Nano FPGA fabric.

```bash
# Install LiteX and DE10-Nano board support
pip install litex litex-boards migen

# Or use the project's managed LiteX environment:
# build/litex-env/ (populated by scripts/fpga/build_de10nano.shs)
```

Build the bitstream:

```bash
# Using project script (recommended):
sh scripts/fpga/build_de10nano.shs

# Or manually:
python3 -m litex_boards.targets.terasic_de10nano \
    --cpu-type=vexriscv_smp \
    --cpu-variant=linux \
    --with-sdcard \
    --build

# Expected output: build/de10nano/gateware/de10nano.sof (~5-10 minutes)
```

---

## 5. Program the DE10-Nano

### Option A: Quartus Programmer (JTAG)

```bash
quartus_pgm -c "USB-Blaster" -m JTAG -o "p;build/de10nano/gateware/de10nano.sof"
```

### Option B: openFPGALoader (recommended, no Quartus GUI needed)

```bash
# Install
sudo apt install openfpgaloader

# Program
openFPGALoader -b de10nano build/de10nano/gateware/de10nano.sof
```

### Option C: Project script

```bash
# Programs bitstream and loads SimpleOS ELF in one step:
sh scripts/fpga/load_elf_de10nano.shs build/simpleos.elf
```

---

## 6. Serial Console

After programming, SimpleOS UART output appears on the first USB serial port:

```bash
# Find the port
ls /dev/ttyUSB*

# Connect (115200 8N1)
picocom -b 115200 /dev/ttyUSB0
# or
screen /dev/ttyUSB0 115200
```

Expected boot output:
```
SimpleOS RISC-V FPGA Boot
UART: 0xf0001000  RAM: 0x40000000 (512MB)
Heap initialized at 0x40200000
Trap vectors installed
Scheduler idle loop running
```

---

## 7. Memory Map (DE10-Nano / LiteX)

| Region | Base Address | Size | Notes |
|--------|-------------|------|-------|
| DRAM | `0x40000000` | 1 GB | DDR3 via LiteDRAM |
| UART | `0xf0001000` | 4 KB | LiteX UART16550 |
| CLINT | `0xf0010000` | 64 KB | Timer + IPI |
| PLIC | `0xf0c00000` | 4 MB | Interrupt controller |
| Heap start | `0x40200000` | — | Configured in `LitexFpgaMemoryMap` |

Source: `src/os/kernel/arch/riscv64/platform/litex_memory_map.spl`

---

## 8. Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| `USB-Blaster not found` | Missing udev rules or cable not reconnected | Re-apply udev rules, replug USB |
| `JTAG chain: 0 devices` | Board not powered, or MSEL switches wrong | Check 5V power LED; MSEL[4:0]=01010 for JTAG |
| `quartus_pgm: command not found` | PATH not set | `source ~/.bashrc` or add Quartus bin to PATH |
| LiteX build fails: `no module named litex_boards` | LiteX not installed | `pip install litex litex-boards` |
| No UART output after boot | Wrong USB port | Try `/dev/ttyUSB1`; DE10-Nano has 2 USB-serial ports |
| `openFPGALoader: permission denied` | udev not loaded | Unplug/replug DE10-Nano USB; check `udevadm trigger` |

---

## Related Files

- `scripts/fpga/build_de10nano.shs` — LiteX build orchestration
- `scripts/fpga/load_elf_de10nano.shs` — Bitstream + ELF load via openocd/GDB
- `src/os/kernel/arch/riscv64/platform/litex_fpga.spl` — DE10-Nano platform capsule
- `src/os/kernel/arch/riscv64/platform/litex_memory_map.spl` — Memory map constants
- `riscv_fpga_simpleos_guide.md` — Overall FPGA SimpleOS guide
