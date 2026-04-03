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

## Current State (2026-04-03)

### Proven
- BGA framebuffer hardware path works (1024x768x32 at 0xFD000000)
- 4 GiB page tables cover VGA LFB
- C-level rendering: desktop background, window, text, taskbar
- Screenshot captured via QMP

### NOT proven (faked in C boot stub)
- The GUI is rendered by C code in `baremetal_stubs.c::_start()`, NOT by the Simple compositor/desktop shell
- `spl_start()` (the compiled Simple entry) still crashes after C rendering
- The Simple code path `gui_entry._start → serial_init → serial_writeln → bga_init_framebuffer → gui_kernel_main` never executes successfully

### Root cause: runtime function gap
- The compiled Simple code calls ~6000 runtime functions (`rt_*`) that don't exist in baremetal
- `auto_stubs.c` provides weak return-0 stubs for all of them — **this masks real breakage**
- Any call to a stubbed function silently returns NIL, causing cascading failures
- String interpolation (`"text {expr}"`) calls `rt_value_to_string` + `rt_string_concat` — now implemented
- But deeper calls (dict, object, type checking, GC) are all stubbed to return 0

### Remaining work to make Simple code drive the GUI
1. **Remove auto_stubs.c** — stop masking failures
2. **Audit which rt_* functions are actually called** on the gui_entry → gui_main path
3. **Implement the minimum set** of runtime functions needed for that path
4. **Or: rewrite gui_entry.spl to avoid runtime-heavy patterns** (no string interpolation, no arrays of complex objects, direct port I/O only)
5. **Verify** spl_start() reaches bga_init_framebuffer() and gui_kernel_main()

## Test Plan

- Serial output shows all `[BOOT]` and `[GUI]` messages from **Simple code** (not C boot stub)
- `spl_start()` completes without crashing
- QEMU screenshot shows GUI rendered by the Simple compositor
- No weak catch-all stubs — every called function must be real
