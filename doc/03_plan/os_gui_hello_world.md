# OS GUI Hello World — Plan

**Date:** 2026-04-03
**Status:** In Progress

## Objective

Enable the SimpleOS x86_64 GUI to boot in QEMU, display a framebuffer, and show a hello world window.

## Current State

- x86_64 builds and boots via Multiboot1 crt0.s
- Serial output works through boot stub C runtime
- Crashes at `spl_start()` because `rt_string_format` returns NULL
- BGA framebuffer never initialized (QEMU shows "Guest has not initialized the display")

## Root Cause

Two stubbed C runtime functions in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`:

1. **`rt_string_format`** — returns 0 (NULL). All string interpolation `"text {expr}"` crashes.
2. **MMIO write naming mismatch** — fb_driver.spl calls `mmio_write32` which routes to `rt_mmio_write32`, but the C implementation may use `rt_mmio_write_u32`.

## Existing Working Components

| Component | File | Status |
|-----------|------|--------|
| Port I/O (x86 asm) | baremetal_stubs.c | Working |
| Serial COM1 | console.spl | Working |
| BGA init (VGA programming) | bga_init.spl | Ready |
| Framebuffer driver | fb_driver.spl | Needs MMIO fix |
| PS/2 keyboard | ps2_keyboard.spl | Ready |
| PS/2 mouse | ps2_mouse.spl | Ready |
| Compositor | compositor.spl | Needs string format |
| Desktop shell | shell.spl | Needs string format |
| GUI entry | gui_entry.spl | Needs string format |
| GUI main | gui_main.spl | Needs string format |

## Implementation Plan

### W1: Fix rt_string_format in baremetal_stubs.c

Implement basic string interpolation support:
- Parse format string for `{}` placeholders
- Convert RuntimeValue args to text (integers → decimal, pointers → hex)
- Concatenate into a new heap-allocated string
- Return tagged RuntimeValue

### W2: Fix MMIO write function linkage

- Verify naming: `rt_mmio_write32` vs `rt_mmio_write_u32`
- Ensure fb_driver.spl's `mmio_write32()` resolves to the real C implementation
- Add any missing MMIO variants

### W3: Build and boot test

- Rebuild with `--source src/os --source src/lib --source examples/simple_os`
- Convert to ELF32 via llvm-objcopy
- Boot in QEMU with VGA std
- Capture screenshot, verify framebuffer initialized

### W4: Hello World window (if compositor works)

- Verify gui_main.spl creates Terminal app window
- If needed, add a minimal hello-world app in the desktop shell app list

## Test Plan

- Serial output shows all `[BOOT]` and `[GUI]` messages
- QEMU screenshot shows non-black display
- Framebuffer shows at least colored rectangles or text
