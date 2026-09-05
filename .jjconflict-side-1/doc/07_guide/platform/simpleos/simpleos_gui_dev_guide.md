## 8. GUI Desktop Environment

### 8.1 Overview

SimpleOS includes a full GUI desktop environment with:
- **Compositor** — glassmorphism window manager with dark/light glass themes
- **Desktop Shell** — taskbar, app launcher, window list, clock, system tray
- **28 GUI Applications** — terminal, editor, calculator, games, system tools
- **Input** — PS/2 keyboard and mouse with drag, focus, shortcuts

### 8.2 Build & Run

```bash
# Build + run GUI desktop (full pipeline)
sh scripts/os_gui.shs

# Build only (no QEMU)
sh scripts/os_gui.shs --build-only

# Run prebuilt kernel
sh scripts/os_gui.shs --run-only

# Run proven glass WM (simpler, no desktop shell)
sh scripts/os_gui.shs --wm

# Clean rebuild
sh scripts/os_gui.shs --clean

# Custom memory
sh scripts/os_gui.shs --mem 4G

# Serial to stdout (for debugging)
sh scripts/os_gui.shs --serial
```

### 8.3 Architecture

```
gui_entry.spl (x86_64 Multiboot entry)
  │
  ├── serial_init() → COM1 at 0x3F8
  ├── bga_init_framebuffer(1024, 768, 32) → BGA VGA
  ├── rt_gui_set_fb() → C runtime glass rendering
  ├── FramebufferDriver.from_boot_info() → MMIO direct-write
  ├── Ps2Keyboard.new().init() → PS/2 keyboard
  ├── Ps2Mouse.create().init() → PS/2 mouse
  ├── Compositor.new(fb, keyboard, mouse)
  ├── DesktopShell.new(compositor).init()
  ├── shell.launch_app("Terminal") × 28 apps
  └── shell.run() → event loop
```

### 8.4 GUI Applications (28)

| Category | Apps |
|----------|------|
| **System** | Terminal, Shell, System Monitor, Disk Manager, Log Viewer, Network Monitor, Package Manager, Settings |
| **Utilities** | Calculator, Clock, Calendar, Memo, Editor, File Manager, File Explorer, Image Viewer, Screenshot, Todo, Hello World, Browser Demo, Color Picker, Font Viewer, Contacts |
| **Games** | Minesweeper, Snake, Tetris, Solitaire |
| **Development** | Hex Editor, Paint |

### 8.5 Keyboard Shortcuts

| Shortcut | Action |
|----------|--------|
| Alt+Tab | Cycle focus between windows |
| Alt+F4 | Close focused window |
| Alt+F5 | Minimize focused window |
| Ctrl+Alt+T | Launch Terminal |
| Ctrl+Alt+H | Launch Hello World |

### 8.6 Entry Points

| Entry | File | Purpose |
|-------|------|---------|
| GUI Desktop | `examples/09_embedded/simple_os/arch/x86_64/gui_entry.spl` | Full desktop shell + all 28 apps |
| Production WM | `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` | DesktopShell through `Engine2dWmFrameExecutor` |
| GPU Test | `examples/09_embedded/simple_os/arch/x86_64/gpu_test_entry.spl` | VirtIO-GPU testing |
| Minimal GUI | `examples/09_embedded/simple_os/arch/x86_64/gui_entry_minimal.spl` | Minimal framebuffer test |

### 8.7 QEMU Configuration

| Parameter | GUI Target | WM Target |
|-----------|-----------|-----------|
| Machine | q35 | q35 |
| CPU | qemu64 | qemu64 |
| Memory | 2G | 512M |
| Display | cocoa | cocoa |
| VGA | std (BGA) | std (BGA) |
| Resolution | 1024x768x32 | 1024x768x32 |

For the board-runnable x86_64 WM verification lane (OVMF pflash → GRUB standalone EFI → multiboot, serial receipt markers, host prerequisites, and troubleshooting), see [`simpleos_x86_64_wm_qemu.md`](simpleos_x86_64_wm_qemu.md).

### 8.8 WM Host Mode Policy

The shared WM runtime supports two host classes:

| Host class | Modes | Evidence |
|------------|-------|----------|
| Windows/macOS/Linux host GUI | Fullscreen and windowed host-WM launch | `scripts/check/check-wm-launch-capture-evidence.shs` host WM package and event-loop checks |
| SimpleOS host | Fullscreen SimpleOS WM only | QEMU MDI framebuffer and RV64 virtio-gpu QMP evidence in `doc/09_report/simpleos_hardening_evidence_matrix_current_2026-07-02.md` |

SimpleOS does not expose a nested host window mode. It owns the framebuffer, so
the SimpleOS WM lane stays full mode until a nested compositor protocol is
designed and tested.
Current live QMP framebuffer evidence is x86_64 SimpleOS WM; RV64 live WM
framebuffer evidence is still a separate missing gate.

### 8.9 Known Issues

- **Cranelift non-determinism**: Clean rebuilds may produce different auto-stub patterns due to HashMap iteration order. Incremental builds are more reliable.
- **Heap exhaustion**: Bump allocator never frees. Long event loop sessions exhaust 512MB heap. Production fix: implement GC or arena allocator.
- **Serial garbling**: `serial_writeln` (Simple function) outputs garbled text (8x character repeat). Use `serial_println` (C extern) for clean output.
- **objcopy required**: QEMU Multiboot1 requires 32-bit ELF. Build produces 64-bit, needs `llvm-objcopy --output-target=elf32-i386` conversion.

### 8.10 Source Layout

```
src/os/
  compositor/     — Window compositor, glass effects, backends
  desktop/        — Desktop shell, app manifest, launcher
  apps/           — 28 GUI applications
  drivers/
    framebuffer/  — BGA init, framebuffer driver
    input/        — PS/2 keyboard, mouse
    gpu/          — VirtIO-GPU acceleration
  services/       — WM service, launcher shortcuts

examples/09_embedded/simple_os/
  arch/x86_64/    — x86_64 entry points, linker script, boot/ C stubs
  src/            — GUI kernel main
```
