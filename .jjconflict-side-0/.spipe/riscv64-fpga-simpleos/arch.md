# Phase 3 Architecture: riscv64-fpga-simpleos

**Date:** 2026-05-19
**Based on:** research.md (Phase 2 gaps), plan doc, existing RV64 arch files

---

## 1. Hardware Manifest SDN Schema

File: `doc/08_tracking/hardware/hardware_manifest.sdn`

This is the canonical board description consumed by the SimpleOS FPGA platform capsule and the linker script generator. Format follows the project SDN convention: `table_name |col_headers|` then 4-space-indented comma rows (strings quoted, integers bare).

```
hardware_manifest |id, field, value, unit, notes|
    0,  board_id,     "zynq7020-ml-carrier", "str",  "ML Carrier Card with Zynq-7020"
    1,  reset_pc,     "0x80000000",           "hex",  "OpenSBI/boot ROM entry point"
    2,  ram_base,     "0x80000000",           "hex",  "DDR start (PS DDR3)"
    3,  ram_size,     "0x20000000",           "hex",  "512 MB"
    4,  uart_base,    "0x10000000",           "hex",  "PL UART0, NS16550-compatible"
    5,  uart_baud,    115200,                 "int",  "baud rate; 115200 default"
    6,  timer_base,   "0x02000000",           "hex",  "CLINT base (mtimecmp/mtime)"
    7,  plic_base,    "0x0C000000",           "hex",  "PLIC base"
    8,  hart_count,   1,                      "int",  "single hart for initial bringup"
    9,  timebase_hz,  10000000,               "int",  "10 MHz CLINT timebase"
```

**Notes on values:**
- `ram_base = 0x80000000` is standard for Zynq-7020 PS DDR (HP0 AXI port).
- `uart_base = 0x10000000` is a VexRiscv-SMP / LiteX SoC conventional PL UART address; adjust to match the actual generated bitstream's address map.
- `timer_base = 0x02000000` follows CLINT convention (`mtime` at `+0xBFF8`, `mtimecmp[0]` at `+0x4000`).
- `plic_base = 0x0C000000` follows standard PLIC convention.
- Agent F is the owner of this file; it generates it from the SoC build or DTB.

---

## 2. Platform Capsule Module Signatures

All four files live under `src/os/kernel/arch/riscv64/platform/`. They follow the same style as `src/os/kernel/boot/uart16550_mmio.spl` and `src/os/kernel/arch/riscv64/trap.spl`.

### 2a. `fpga.spl` — Top-level FPGA platform init

**Module path:** `os.kernel.arch.riscv64.platform.fpga`

```
use os.kernel.arch.riscv64.platform.manifest.{BoardConfig, load_board_config}
use os.kernel.arch.riscv64.platform.uart_mmio.{uart_mmio_init, uart_mmio_puts}
use os.kernel.arch.riscv64.platform.timer_mmio.{timer_mmio_init}

struct FpgaPlatform:
    config: BoardConfig

impl FpgaPlatform:
    fn uart_puts(msg: text):
        uart_mmio_puts(self.config.uart_base, msg)

fn fpga_platform_init(manifest_path: text) -> FpgaPlatform:
    """Load manifest, initialize UART and timer, return platform handle."""

fn fpga_platform_init_default() -> FpgaPlatform:
    """Init from compile-time embedded manifest (no filesystem required)."""
```

**Responsibilities:**
- Call `load_board_config()` to get addresses.
- Call `uart_mmio_init(config.uart_base, config.uart_baud)`.
- Call `timer_mmio_init(config.timer_base)`.
- Return `FpgaPlatform` with the loaded `BoardConfig`.
- Must NOT assume any virtio, DTB, or SBI firmware calls (FPGA baremetal only).

---

### 2b. `manifest.spl` — Hardware manifest parser

**Module path:** `os.kernel.arch.riscv64.platform.manifest`

```
struct BoardConfig:
    board_id:    text
    reset_pc:    u64
    ram_base:    u64
    ram_size:    u64
    uart_base:   u64
    uart_baud:   u64
    timer_base:  u64
    plic_base:   u64
    hart_count:  u64
    timebase_hz: u64

fn load_board_config_from_sdn(sdn_text: text) -> BoardConfig:
    """Parse hardware_manifest SDN text, return BoardConfig."""

fn default_board_config() -> BoardConfig:
    """Compile-time constant config for zynq7020-ml-carrier (fallback if no SDN)."""

fn load_board_config() -> BoardConfig:
    """Production entry: returns default_board_config() until filesystem is available."""
```

**Notes:**
- `default_board_config()` returns the values from Section 1 above, hardcoded as compile-time constants. This is the only path available at early boot (no_fs profile).
- `load_board_config_from_sdn()` is for later phases when initramfs or block device is available.
- No `use std.*` imports that pull in GC or allocator — noalloc-compatible.

---

### 2c. `uart_mmio.spl` — MMIO UART driver

**Module path:** `os.kernel.arch.riscv64.platform.uart_mmio`

Wraps `src/os/kernel/boot/uart16550_mmio.spl` with a manifest-aware interface. Does not duplicate register constants — re-exports or delegates.

```
use os.kernel.boot.uart16550_mmio.{
    uart16550_mmio_init, uart16550_mmio_write_byte, uart16550_mmio_read_byte
}

fn uart_mmio_init(base: u64, baud: u64):
    """Initialize NS16550-compatible UART at base for given baud rate."""

fn uart_mmio_putchar(base: u64, ch: u8):
    """Write single byte, blocking until TX FIFO empty."""

fn uart_mmio_getchar(base: u64) -> u8?:
    """Read single byte if RX data ready; nil otherwise."""

fn uart_mmio_puts(base: u64, msg: text):
    """Write null-terminated string byte-by-byte."""

fn uart_mmio_puts_hex(base: u64, label: text, val: u64):
    """Write 'label=0xVALUE\n' for boot diagnostics."""
```

**Notes:**
- `uart_mmio_init` with a `baud` parameter differs from the existing `uart16550_mmio_init` (which hardcodes 115200 via divisor 0x01). The FPGA variant must compute the divisor from `timebase_hz / baud / 16` using the manifest's `uart_baud` field — or accept the divisor pre-computed.
- `uart_mmio_puts_hex` is needed for the boot proof string: `SIMPLE-RV64-FPGA-HELLO board=<id> hart=0 pc=<addr>`.
- All functions are noalloc-safe (no heap allocation).

---

### 2d. `timer_mmio.spl` — CLINT-compatible MMIO timer

**Module path:** `os.kernel.arch.riscv64.platform.timer_mmio`

```
# CLINT register offsets (standard)
val CLINT_MSIP_BASE:     u64 = 0x0000   # machine software interrupt pending (per-hart)
val CLINT_MTIMECMP_BASE: u64 = 0x4000   # mtimecmp[hart] (8 bytes per hart)
val CLINT_MTIME:         u64 = 0xBFF8   # mtime counter (64-bit)

fn timer_mmio_init(clint_base: u64):
    """Disable software interrupts; leave mtime running."""

fn timer_read_mtime(clint_base: u64) -> u64:
    """Read current 64-bit mtime counter value."""

fn timer_set_mtimecmp(clint_base: u64, hart: u64, deadline: u64):
    """Set mtimecmp[hart] to deadline, arming the timer interrupt."""

fn timer_clear_mtimecmp(clint_base: u64, hart: u64):
    """Set mtimecmp[hart] to u64::MAX, disabling timer interrupt for hart."""

fn timer_polling_delay_us(clint_base: u64, timebase_hz: u64, us: u64):
    """Busy-wait for approximately us microseconds using mtime."""

fn timer_polling_delay_ms(clint_base: u64, timebase_hz: u64, ms: u64):
    """Busy-wait for approximately ms milliseconds using mtime."""
```

**Notes:**
- `timer_polling_delay_*` are the only timer primitives required for `riscv64-fpga-min` profile (polling_timer feature flag, no interrupt).
- All reads/writes go through `mmio_read64` / `mmio_write64` from `os.kernel.boot.mmio`.
- Uses `u64::MAX = 0xFFFF_FFFF_FFFF_FFFF` to disarm timer.

---

## 3. Boot Profile Definition: `riscv64-fpga-min`

### 3a. Target Contract

File to modify: `src/compiler/70.backend/backend/riscv_target.spl`

Add a new constructor following the existing `riscv_linux_target_contract` pattern:

```
fn riscv_fpga_target_contract() -> RiscvTargetContract:
    """Baremetal RV64 FPGA target — no OS, no SBI firmware calls, polling timer."""
    RiscvTargetContract(
        target: CodegenTarget.Riscv64,
        arch: "riscv64",
        vendor: "unknown",
        os: "none",
        env: nil,
        abi: RiscvTargetAbi.LP64,
        abi_text_value: "lp64",
        cpu: "generic-rv64",
        features: ["+m", "+a", "+c"],
        march: "rv64imac",
        linker: "riscv64-unknown-elf-ld",
        sysroot: "",
        crt_dir: "",
        pointer_bits: 64,
        stack_align_bytes: 16,
        arg_register_count: 8,
        call_plt_reloc: 0
    )
```

**Triple:** `riscv64-unknown-none`
**ABI:** `lp64` (no FPU required for initial bringup; upgrade to `lp64d` when softcore includes F/D extensions)
**march:** `rv64imac` (integer, multiply, atomic, compressed — conservative for VexRiscv-SMP or Rocket minimal config)

Also add `preset_riscv64_fpga` in `src/compiler/70.backend/target_presets.spl` analogous to `preset_riscv32_baremetal`.

### 3b. Linker Script Differences from QEMU virt

New file: `src/os/kernel/arch/riscv64/platform/fpga_linker.ld`

Key differences from `src/os/kernel/arch/riscv64/linker.ld`:

| Property | QEMU virt | FPGA (riscv64-fpga-min) |
|----------|-----------|------------------------|
| RAM ORIGIN | `0x80200000` (after OpenSBI 2MB) | `0x80000000` (no OpenSBI reservation) |
| RAM LENGTH | `126M` | `510M` (512MB minus 2MB BRAM boot area) |
| BRAM region | absent | `BRAM (rx) : ORIGIN = 0x00000000, LENGTH = 64K` |
| Heap size | `16M` | `4M` (conservative for initial smoke) |
| Stack size | `64K` | `32K` (single-hart minimal) |

Full MEMORY block:

```
MEMORY {
    BRAM (rx)  : ORIGIN = 0x00000000, LENGTH = 64K
    RAM  (rwx) : ORIGIN = 0x80000000, LENGTH = 510M
}
```

`.text.entry` and trap vector load into `RAM`; BRAM is reserved for the boot ROM image (separate binary, not part of the SimpleOS ELF).

### 3c. Feature Flags

Defined in `src/os/kernel/arch/riscv64/platform/fpga.spl` as compile-time constants:

| Flag | Value | Effect |
|------|-------|--------|
| `no_fs` | true | No VFS, no block driver, no FAT32 mount |
| `no_net` | true | No TCP/IP stack, no virtio-net |
| `no_fb` | true | No framebuffer, no GPU, no display |
| `polling_timer` | true | Uses `timer_polling_delay_*` instead of timer interrupt |
| `initramfs_only` | true | Payload is compiled-in (no disk image required) |
| `uart_console_only` | true | Only UART output, no VGA/serial mux |

---

## 4. Bare-Metal Hello Payload Layout

Directory: `examples/09_embedded/fpga_riscv/rv64_fpga_hello/`

```
examples/09_embedded/fpga_riscv/rv64_fpga_hello/
├── hello.S              # RV64 assembly startup + UART write
├── linker.ld            # Fixed-address linker for FPGA BRAM/DDR
├── build.shs            # Build script (riscv64-unknown-elf-gcc / objcopy)
└── README.md            # (only if explicitly requested)
```

### `hello.S` — RV64 bare-metal startup

Minimal entry:
1. Set `sp` to `_stack_top` (defined in linker.ld).
2. Zero `.bss`.
3. Write proof string via UART MMIO at `UART_BASE` (macro from linker symbol or hardcoded to `0x10000000`).
4. Proof string format: `SIMPLE-RV64-FPGA-HELLO board=zynq7020-ml-carrier hart=0 pc=0x80000000\r\n`
5. Infinite `wfi` loop after output.

Trap vector: minimal `mtvec` pointing to a single `j .` (halt) — not a full trap handler.

### `linker.ld` — Fixed-address FPGA

```
OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 4M
}

SECTIONS {
    .text : { KEEP(*(.text.entry)) *(.text*) } > RAM
    .rodata : { *(.rodata*) } > RAM
    .data   : { *(.data*) } > RAM
    .bss (NOLOAD) : { _sbss = .; *(.bss*) *(COMMON) _ebss = .; } > RAM
    .stack (NOLOAD) : ALIGN(16) { _stack_bottom = .; . += 16K; _stack_top = .; } > RAM
}
```

### `build.shs` — Build script

```sh
#!/usr/bin/env sh
# build.shs — build rv64_fpga_hello bare-metal ELF + binary
CROSS=riscv64-unknown-elf
${CROSS}-gcc -march=rv64imac -mabi=lp64 -nostdlib -nostartfiles \
    -T linker.ld hello.S -o rv64_fpga_hello.elf
${CROSS}-objcopy -O binary rv64_fpga_hello.elf rv64_fpga_hello.bin
echo "BUILT: rv64_fpga_hello.elf rv64_fpga_hello.bin"
```

### Expected output

```
SIMPLE-RV64-FPGA-HELLO board=zynq7020-ml-carrier hart=0 pc=0x80000000
```

The `pc` value is the reset vector address from `hardware_manifest.sdn` field `reset_pc`.

---

## 5. Phase 5 File Scope Partition

Disjoint ownership prevents parallel agent conflicts. No two agents may write to the same directory.

### Agent A (Scripts + Hardware Tracking)
- `scripts/check-riscv64-fpga-simpleos-preflight.shs` — preflight inventory script
- `scripts/jtag-ftdi-unbind.shs` — JTAG FTDI unbind/rebind helper
- `doc/08_tracking/hardware/` — hardware log files, `hardware_manifest.sdn`

### Agent C (Platform Capsules)
- `src/os/kernel/arch/riscv64/platform/fpga.spl`
- `src/os/kernel/arch/riscv64/platform/manifest.spl`
- `src/os/kernel/arch/riscv64/platform/uart_mmio.spl`
- `src/os/kernel/arch/riscv64/platform/timer_mmio.spl`
- `src/os/kernel/arch/riscv64/platform/fpga_linker.ld`

**Must not touch** existing files in `src/os/kernel/arch/riscv64/` outside the new `platform/` subdir.

### Agent D (Bare-Metal Hello Payload)
- `examples/09_embedded/fpga_riscv/rv64_fpga_hello/` (entire new subdirectory)

**Must not touch** any `src/` or `test/` files.

### Agent E (Test Harness)
- `test/riscv64_fpga/` (new test directory)
  - `test/riscv64_fpga/preflight_spec.spl` — checks AC-1, AC-2, AC-3
  - `test/riscv64_fpga/manifest_spec.spl` — checks AC-6 (manifest parse)
  - `test/riscv64_fpga/platform_build_spec.spl` — checks AC-4, AC-5 (build-time)
  - `test/riscv64_fpga/hello_build_spec.spl` — checks AC-7 (ELF builds, proof string)
  - `test/riscv64_fpga/blocked_gates_spec.spl` — checks AC-8 (BLOCKED emission)

**Must not touch** `src/` files.

### Agent F (Profile + Preset)
- `src/compiler/70.backend/backend/riscv_target.spl` — add `riscv_fpga_target_contract()`
- `src/compiler/70.backend/target_presets.spl` — add `preset_riscv64_fpga()`
- `doc/08_tracking/hardware/hardware_manifest.sdn` — canonical SDN file (coordinate with Agent A; Agent F writes it, Agent A reads it)

**Note:** Agent F touches `riscv_target.spl` which Agent C does NOT touch. Explicit boundary.

---

## 6. Verification Notes

### AC-5: Boot profile (`riscv64-fpga-min`)
Build-time verifiable. Test emits PASS if `riscv_fpga_target_contract()` compiles and linker script exists with correct ORIGIN. Does NOT require FPGA hardware.

### AC-7: Bare-metal hello payload
Build-time verifiable. Test emits PASS if `rv64_fpga_hello.elf` builds successfully and `strings rv64_fpga_hello.elf | grep SIMPLE-RV64-FPGA-HELLO` matches. Does NOT require FPGA hardware.

### AC-9: QEMU regression
Build-time + QEMU simulation verifiable. Existing QEMU RV64 smoke test must still pass. The FPGA platform capsule is compiled only when `--target riscv64-fpga` is active; no existing QEMU paths are modified.

### Hardware-gated ACs (must emit BLOCKED, not PASS/FAIL)
These require physical synthesis tools and/or connected hardware:

| AC | Gate condition | BLOCKED reason text |
|----|---------------|---------------------|
| AC-1 (preflight) | Hardware board not connected | `BLOCKED: no FT4232H USB device found (lsusb 0403:6011 absent)` |
| AC-2 (inventory log) | Hardware board not connected | `BLOCKED: hardware inventory requires connected board` |
| AC-3 (JTAG unbind) | Hardware board not connected | `BLOCKED: JTAG unbind requires connected FT4232H device` |
| AC-5 (FPGA UART transcript) | Synthesis tools (vivado/yosys) absent | `BLOCKED: riscv64-fpga-min FPGA upload requires vivado or openFPGALoader` |
| AC-7 (FPGA UART transcript) | Physical board absent | `BLOCKED: UART proof requires connected FPGA board` |
| AC-9 (hardware boot markers) | Physical board absent | `BLOCKED: SimpleOS FPGA boot markers require connected board` |

Tests must check for the blocking condition first and emit `BLOCKED: <reason>` via the spipe harness's `skip_blocked(reason)` mechanism. They must NOT probe hardware and silently time-out or emit false PASS.

**Cross-compiler gate:** AC-7 build test must also emit `BLOCKED: riscv64-unknown-elf-gcc not found` if the cross toolchain is absent (rather than failing with a build error).
