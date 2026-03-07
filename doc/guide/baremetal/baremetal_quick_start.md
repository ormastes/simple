# Bare-Metal Quick Start Guide

This guide shows how to build and run Simple programs on bare-metal hardware (no operating system).

## Prerequisites

### ARM Cortex-M
```bash
sudo apt install gcc-arm-none-eabi qemu-system-arm
```

### x86_64
```bash
sudo apt install qemu-system-x86
# Standard GNU binutils (ld, as) usually already installed
```

### RISC-V
```bash
sudo apt install gcc-riscv64-unknown-elf qemu-system-riscv64
```

## Quick Start

### List Available Targets

```bash
simple build baremetal --list-targets
```

Output:
```
Available bare-metal targets:
  arm      - ARM Cortex-M (QEMU versatilepb)
  x86_64   - x86_64 with multiboot2 (QEMU)
  riscv    - RISC-V 64-bit (QEMU virt)
```

### Build for Target

The basic workflow:

1. **Write your Simple program** (e.g., `hello.spl`)
2. **Build for target**: `simple build baremetal --target=<arch> hello.spl`
3. **Run in QEMU**: Use platform-specific QEMU command

Currently, compilation step returns:
```
Compilation not yet implemented - needs Simple compiler with bare-metal backend
```

This is expected. The build system is integrated, but the compiler backend integration is **future work**.

## Platform-Specific Details

### ARM Cortex-M

**Target:** `--target=arm`

**Memory Layout:**
- Flash: `0x08000000` (512KB)
- RAM: `0x20000000` (128KB)

**Build Command:**
```bash
simple build baremetal --target=arm examples/blink_led.spl
```

**QEMU Command:**
```bash
qemu-system-arm -M versatilepb -nographic -serial stdio \
  -kernel build/baremetal-arm/kernel.elf
```

**Hardware Support:**
- STM32F4xx (Cortex-M4F)
- LM3S6965 (Cortex-M3)
- Any Cortex-M with 128KB+ RAM

**Example: Blink LED**
```simple
# examples/blink_led.spl
# Blink LED on GPIO (platform-specific)

extern fn delay_ms(ms: i64)
extern fn gpio_set(pin: i64, state: bool)

fn main():
    var count = 0
    while count < 10:
        gpio_set(13, true)   # LED on
        delay_ms(500)
        gpio_set(13, false)  # LED off
        delay_ms(500)
        count = count + 1
```

### x86_64

**Target:** `--target=x86_64`

**Memory Layout:**
- Load address: `0x00100000` (1MB)
- Stack: `0x00200000` (grows down)
- Heap: 16MB

**Build Command:**
```bash
simple build baremetal --target=x86_64 examples/uart_echo.spl
```

**QEMU Command:**
```bash
qemu-system-x86_64 -kernel build/baremetal-x86_64/kernel.elf \
  -serial stdio -display none \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

**Boot Protocol:** Multiboot2 (compatible with GRUB2)

**Example: UART Echo**
```simple
# examples/uart_echo.spl
# Echo characters back over serial port

extern fn uart_read() -> i64
extern fn uart_write(ch: i64)

fn main():
    while true:
        val ch = uart_read()
        if ch != -1:
            uart_write(ch)
```

### RISC-V 64-bit

**Target:** `--target=riscv`

**Memory Layout:**
- RAM start: `0x80000000`
- Load address: `0x80000000`
- Stack: `0x80200000` (grows down)
- Heap: 32MB

**Build Command:**
```bash
simple build baremetal --target=riscv examples/interrupt_demo.spl
```

**QEMU Command:**
```bash
qemu-system-riscv64 -M virt -bios none -nographic \
  -serial stdio -kernel build/baremetal-riscv/kernel.elf
```

**Features:**
- Multi-hart support (SMP)
- Device tree blob preserved
- Machine mode interrupts

**Example: Interrupt Handler**
```simple
# examples/interrupt_demo.spl
# Handle timer interrupts

var tick_count: i64 = 0

extern fn enable_interrupts()
extern fn set_timer(cycles: i64)

# Interrupt handler (called from trap_vector)
fn timer_interrupt_handler():
    tick_count = tick_count + 1
    set_timer(1000000)  # Next tick in 1M cycles

fn main():
    enable_interrupts()
    set_timer(1000000)

    while tick_count < 10:
        pass_do_nothing  # Wait for interrupts
```

## Linker Scripts

Each platform has a custom linker script defining memory layout:

- **ARM**: `src/compiler/baremetal/arm/linker.ld`
- **x86_64**: `src/compiler/baremetal/x86_64/linker.ld`
- **RISC-V**: `src/compiler/baremetal/riscv/linker.ld`

### Key Sections

**ARM Linker Script:**
```ld
MEMORY {
    FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 512K
    RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 128K
}

SECTIONS {
    .vector_table : { ... } > FLASH
    .text         : { ... } > FLASH
    .data         : { ... } > RAM
    .bss          : { ... } > RAM
    .heap         : { ... } > RAM
    .stack        : { ... } > RAM
}
```

## Startup Code

Each platform has assembly startup code (`crt0.s`):

**ARM (`src/compiler/baremetal/arm/crt0.s`):**
- Vector table with initial stack pointer
- Reset handler: copy `.data`, zero `.bss`, enable FPU
- Default exception handlers
- Entry point: `reset_handler`

**x86_64 (`src/compiler/baremetal/x86_64/crt0.s`):**
- Multiboot2 header
- 32-bit to 64-bit mode transition
- Page table setup (identity-mapped 1GB)
- GDT loading
- Entry point: `_start`

**RISC-V (`src/compiler/baremetal/riscv/crt0.s`):**
- Multi-hart initialization (hart 0 runs, others park)
- Trap vector setup
- BSS zeroing, `.data` copy
- Device tree blob preservation
- Entry point: `_start`

## Testing in QEMU

### Exit Codes

Bare-metal programs can signal exit codes to QEMU using the **isa-debug-exit** device:

**x86_64 Exit Example:**
```asm
# Exit with code 0 (success)
mov $0xf4, %dx     # isa-debug-exit port
mov $0, %ax        # Exit code 0
out %ax, %dx
```

**Exit code transformation:** `actual = (qemu_exit - 1) / 2`
- QEMU exit 1 → actual 0 (success)
- QEMU exit 3 → actual 1 (failure)

### Serial Output

All platforms redirect serial to stdio (`-serial stdio`):

```simple
extern fn uart_puts(s: text)

fn main():
    uart_puts("Hello from bare-metal!\n")
```

### Test Format

Use SSpec-compatible output for automated testing:

```simple
fn main():
    uart_puts("[TEST START]\n")

    if run_test_1():
        uart_puts("[PASS] test_1\n")
    else:
        uart_puts("[FAIL] test_1: assertion failed\n")

    uart_puts("[TEST END] passed=1 failed=0\n")
```

## Future Work

1. **Compiler Integration** - Connect Simple compiler to bare-metal backend
2. **Runtime Library** - Minimal runtime for bare-metal (allocator, UART, GPIO)
3. **Board Support Packages** - Pre-configured profiles for common boards
4. **Debugging Support** - GDB integration, remote debugging
5. **Flash Programming** - OpenOCD/st-link integration for real hardware

## Troubleshooting

### Build Errors

**"Linker script not found"**
- Verify files exist: `ls src/compiler/baremetal/*/linker.ld`
- All three linker scripts should be present

**"Startup code not found"**
- Verify files exist: `ls src/compiler/baremetal/*/crt0.s`
- All three crt0.s files should be present

**"Assembly failed"**
- Install target toolchain (see Prerequisites)
- ARM: `gcc-arm-none-eabi`
- RISC-V: `gcc-riscv64-unknown-elf`

### QEMU Errors

**"qemu-system-* not found"**
```bash
# Ubuntu/Debian
sudo apt install qemu-system-arm qemu-system-x86 qemu-system-riscv

# macOS
brew install qemu
```

**QEMU hangs (no output)**
- Ensure `-serial stdio` flag is present
- Check kernel has UART output code
- Verify entry point matches linker script

**"VNC server running on..."**
- Add `-display none` to disable graphical output

## Resources

- **ARM Cortex-M Programming**: ARM Architecture Reference Manual
- **x86_64 Bare-Metal**: OSDev Wiki (https://wiki.osdev.org)
- **RISC-V Spec**: RISC-V Privileged Architecture Spec
- **QEMU Documentation**: https://www.qemu.org/docs/master/

## Examples Repository

Full working examples coming soon:
- `examples/baremetal/blink_led_arm.spl`
- `examples/baremetal/uart_echo_x86.spl`
- `examples/baremetal/interrupt_riscv.spl`
- `examples/baremetal/multitasking_demo.spl`
