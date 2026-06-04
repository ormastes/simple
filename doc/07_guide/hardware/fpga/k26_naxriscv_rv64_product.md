# K26 NaxRiscv RV64 SoC — Product Guide

## 1. Board Identity

| Item | Value |
|------|-------|
| SOM | Kria K26 (XCZU5EV Zynq UltraScale+ MPSoC) |
| Carrier | ML Carrier Card (KV260) |
| USB JTAG | FT4232H — VID:PID `0403:6011`, serial `XFL1OSWWFM2B` |

## 2. Architecture

Hybrid PS-clock + PL-CPU design:

- **PS provides FCLK_CLK0 (100 MHz) only** — no PS CPU is used at runtime.
- **NaxRiscv RV64** runs entirely in PL as the main CPU.
- **JTAG UART** via BSCANE2 primitive for console I/O.
- **64 KB integrated SRAM**.
- **LiteX SoC** with BIOS (prints banner + console on JTAG UART).

## 3. Memory Map

From LiteX build output:

| Region | Base | Size | Notes |
|--------|------|------|-------|
| ROM | `0x00000000` | 128 KB | Boot ROM |
| SRAM | `0x10000000` | 8 KB | Scratchpad |
| OpenSBI | `0x40f00000` | 512 KB | SBI firmware |
| Main RAM | `0x80000000` | 2 GB | IO region |
| CLINT | `0xf0010000` | 64 KB | Timer |
| PLIC | `0xf0c00000` | 4 MB | Interrupts |
| CSR | `0xf0000000` | 64 KB | Control/Status |

## 4. Build Target

Build script: `build/k26_naxriscv_rv64.py`

### Environment setup and build command

```bash
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH="$JAVA_HOME/bin:$HOME/.local/sbt/bin:$PATH"
source build/litex-venv/bin/activate
source /home/ormastes/Xilinx/2025.2/Vivado/settings64.sh
python3 build/k26_naxriscv_rv64.py --build --xlen 64
```

### Build phases

1. **sbt / SpinalHDL** generates NaxRiscv Verilog.
2. **LiteX** compiles BIOS.
3. **Vivado** synthesis, implementation, and bitstream generation.

### Output

```
build/build/xilinx_kv260/gateware/xilinx_kv260.bit
```

## 5. Vivado Device Requirement

The Zynq UltraScale+ MPSoC device family must be installed in Vivado. See `vivado_device_setup.md` for installation instructions.

## 6. Dependencies

All dependencies reside in `litex-venv`:

| Dependency | Version / Notes |
|------------|-----------------|
| sbt | 1.10.7 |
| Java | 8 (OpenJDK) — Scala 2.12.18 |
| pythondata-cpu-naxriscv | NaxRiscv at commit `9f452d5` |
| pythondata-software-picolibc | picolibc data package |
| pythondata-software-compiler_rt | compiler-rt data package |
| meson | Build system for picolibc/compiler_rt |

## 7. Programming and Monitor

```bash
# Unbind JTAG from ftdi_sio
sh scripts/fpga/jtag-ftdi-unbind.shs

# Program via openFPGALoader
openFPGALoader -c ft4232 --detect
openFPGALoader -c ft4232 build/build/xilinx_kv260/gateware/xilinx_kv260.bit

# Monitor JTAG UART
litex_term jtag
```

## 8. Expected Output

LiteX BIOS banner with NaxRiscv RV64 identification, followed by an interactive console on JTAG UART.

## 9. Known Issues

- **Vivado device family**: Zynq UltraScale+ MPSoC is not installed by default; must be added via Vivado installer.
- **migen tracer**: Python 3.12 incompatibility with raw bytecode inspection (patched locally).
- **JTAGPHY xck prefix**: Missing `xck` entry in BSCANE2 device list (patched locally).
- **sbt Java version**: Requires Java 8; Java 21 causes build failures.
- **picolibc / compiler_rt**: Circular import during `pip install` of data packages.

## 10. Local Patches Applied

These patches live in `litex-venv` and are not upstreamed:

| File | Change |
|------|--------|
| `migen/fhdl/tracer.py` | Replaced raw bytecode inspection with `dis` module for Python 3.12 compatibility. |
| `litex/soc/cores/jtag.py` | Added `xck` to BSCANE2 device list and TDI delay dict. |

## 11. Related Files

| Purpose | Path |
|---------|------|
| Build script | `build/k26_naxriscv_rv64.py` |
| Hardware inventory | `doc/08_tracking/hardware/riscv64_fpga_inventory_2026-05-19.md` |
| Hardware manifest | `doc/08_tracking/hardware/hardware_manifest.sdn` |
| Bare-metal hello | `examples/09_embedded/fpga_riscv/rv64_fpga_hello/` |
| Preflight check | `scripts/check/check-riscv64-fpga-simpleos-preflight.shs` |
