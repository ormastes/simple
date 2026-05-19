# rv64_fpga_hello — RV64 Bare-Metal FPGA Hello Payload

Minimal RV64 bare-metal proof payload for the ML Carrier Card (Kria K26 / XCZU5EV).
Boots at 0x80000000, prints a proof string over UART, then emits tick markers.

## Files

| File | Purpose |
|------|---------|
| `startup.S` | RV64 assembly entry: sp init, BSS clear, hart park, call main |
| `main.c` | UART 16550 helpers + proof string + tick loop |
| `linker.ld` | Fixed-address linker script (DDR @ 0x80000000, BRAM @ 0x00000000) |
| `build.shs` | Build script (sh); auto-detects riscv64-unknown-elf or riscv64-linux-gnu |
| `Makefile` | Thin wrapper: `make all`, `make clean`, `make flash` (BLOCKED) |

## Build Requirements

- `riscv64-unknown-elf-gcc` (preferred) **or** `riscv64-linux-gnu-gcc`
- Toolchain build flags: `-march=rv64imac -mabi=lp64 -nostdlib -mcmodel=medany`

Install on Ubuntu/Debian:
```sh
sudo apt install gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf
```

Or build from source:
```
https://github.com/riscv-collab/riscv-gnu-toolchain
```

## Build

```sh
sh build.shs          # produces rv64_fpga_hello.elf + rv64_fpga_hello.bin
make                  # same via Makefile
make clean            # remove artefacts
```

Override UART base address if needed:
```sh
UART_BASE=0x60000000 sh build.shs
```

## Memory Map

| Region | Base | Size | Use |
|--------|------|------|-----|
| DDR | `0x80000000` | 64 MB | Code + data + stack |
| BRAM | `0x00000000` | 64 KB | Reserved (unused in this payload) |
| UART MMIO | `0x10000000` | 4 KB | NS16550-compatible UART |
| Stack | top of `.stack` section | 16 KB | Grows down from `_stack_top` |

Load address: `0x80000000` — the soft-core reset vector must point here.

## Expected Output

```
SIMPLE-RV64-FPGA-HELLO board=xck26-ml-carrier hart=0 pc=0x80000000
TICK 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
TICK 16 17 ...
```

(Exact PC value in the proof string will vary by link address.)

## Flashing (BLOCKED — hardware required)

Flash via OpenOCD + JTAG probe:
```sh
openocd -f board/ml_carrier_card.cfg
# in OpenOCD console:
load_image rv64_fpga_hello.elf 0x80000000 elf
resume 0x80000000
```

See `doc/03_plan/agent_tasks/riscv64_fpga_simpleos_launch.md` for full hardware
bringup procedure.
