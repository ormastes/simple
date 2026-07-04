# SimpleOS Package Manager & Installer GUI Design

## Overview

Three glass-themed GUI applications for SimpleOS package infrastructure:

1. **Package Manager** — Browse, install, remove, update packages
2. **OS Installer** — Multi-step wizard for fresh OS installation from USB
3. **Software Update** — macOS-style upgrade panel for existing installations

All share a common core (`pkg_core.spl`) and the glass design system.

## Architecture — Minimized Duplication

```
┌──────────────────────────────────────────────────┐
│                  pkg_core.spl                     │
│  (PackageInfo, PkgCore, install/remove/update)    │
├──────────┬──────────┬──────────┬─────────────────┤
│ CLI      │ GUI Pkg  │ GUI      │ GUI Upgrade     │
│ pkg_cli  │ Manager  │ Installer│ upgrade_gui     │
│ .spl     │ .spl     │ _gui.spl │ .spl            │
│          │          │          │                  │
│ prints   │ builder  │ builder  │ builder API     │
│ text     │ API +    │ API +    │ + glass theme   │
│          │ glass    │ glass    │                  │
│          │          │          │ install_dialog   │
│          │          │          │ .spl (shared)    │
└──────────┴──────────┴──────────┴─────────────────┘
```

**Shared components:**
- `pkg_core.spl` — All operations (no duplication between CLI and GUI)
- `install_dialog.spl` — Reusable install/remove dialogs (used by PackageManager and standalone)
- `usb_installer.spl` — Disk detection and partition logic (used by CLI installer and GUI installer)

## Design System: Glass Dark

Based on existing `glass_tokens.spl` and `glass_numeric_tokens.spl`:

| Token | Value | Usage |
|-------|-------|-------|
| Background top | `#060612` | Deep space gradient start |
| Background bottom | `#1A0830` | Purple gradient end |
| Surface | `#1E1E23` @ 72% | Glass panel background |
| Elevated | `#2C2C32` @ 88% | Active/focused surfaces |
| Text primary | `#F5F5F7` | Main text |
| Text secondary | `#EBEBF5` @ 60% | Dim labels |
| Accent | `#0A84FF` | iOS blue (buttons, links) |
| Accent 2 | `#BB86FC` | Purple (progress, highlights) |
| Error | `#FF453A` | Error states |
| Success | `#30D158` | Success checkmarks |
| Blur radius | 12–20px | Glass blur effect |
| Corner radius | 8–16px | Rounded corners |

## 1. Package Manager UI

### Layout (Desktop)

```
┌──────────────────────────────────────────────────────────┐
│ [Package]  [View]  [Help]                                │  Menubar
├──────────────────────────────────────────────────────────┤
│ [Installed]  [Available]  [Updates]                      │  Tabs
├──────────────────────────────────────────────────────────┤
│ [All] [System] [Dev] [Utils] [Network] [Games]          │  Category
├──────────────────────────────────────────────────────────┤
│ Filter: All                                              │
├────────────────────────────────────┬─────────────────────┤
│ [Install] [Update All] [Refresh]   │  Package Details    │
│                                    │                     │
│  Name        Ver   Size  Status    │  Name: simple-editor│
│ ▸ editor     2.1   3.2M  Inst     │  Version: 2.1.0     │
│   calc       1.0   0.3M  Inst     │  Size: 3.2 MB       │
│   browser    0.7   9.6M  Upd      │  Category: Utils    │
│                                    │  Status: installed  │
│                                    │                     │
│                                    │  Dependencies:      │
│                                    │    - simpleos-core  │
├────────────────────────────────────┴─────────────────────┤
│ [Installing editor... [########....] 67%]                │  Progress
├──────────────────────────────────────────────────────────┤
│ Installed: 12 | Available: 8 | Updates: 3    12 shown    │  Statusbar
└──────────────────────────────────────────────────────────┘
```

### Install Dialog (overlay)

```
┌─────────────────────────────────────┐
│  Install simple-editor?             │
│                                     │
│  Package: simple-editor             │
│  Version: 2.1.0                     │
│  Size: 3.2 MB                       │
│                                     │
│  Dependencies (2):                  │
│    + simpleos-core                  │
│    + simple-fs                      │
│                                     │
│  ─────────────────────────────────  │
│  [Install (y)]      [Cancel (n)]    │
└─────────────────────────────────────┘
```

## 2. OS Installer Wizard

### Layout (macOS Installer Style)

```
┌──────────────────────────────────────────────────────────┐
│  SimpleOS Installer                    [####.......] 43% │
├───────────┬──────────────────────────────────────────────┤
│           │                                              │
│   Steps   │  Welcome / License / Disk / etc.             │
│           │                                              │
│  ✓ Welcome│  ╔══════════════════════════════╗            │
│  ✓ License│  ║      SimpleOS v1.0.0         ║            │
│ ▸ Disk    │  ║                              ║            │
│  ○ Part   │  ║  A modern, glass-themed OS   ║            │
│  ○ Install│  ╚══════════════════════════════╝            │
│  ○ Config │                                              │
│  ○ Done   │  This wizard will guide you through          │
│           │  installing SimpleOS on your computer.       │
│           │                                              │
├───────────┴──────────────────────────────────────────────┤
│  [← Back]                                    [Next →]    │
└──────────────────────────────────────────────────────────┘
```

### Steps

| # | Step | Content |
|---|------|---------|
| 1 | Welcome | Logo, version, system requirements |
| 2 | License | Scrollable MIT license + accept checkbox |
| 3 | Disk Select | Table of detected disks (VirtIO/NVMe/SATA) |
| 4 | Partition | GPT plan table (EFI + Root + Swap), erase warning |
| 5 | Installing | Per-package progress, log scroll |
| 6 | Configure | Hostname, username, timezone fields |
| 7 | Complete | Success banner, reboot button |

## 3. Software Update GUI

### Layout (macOS Software Update Style)

```
┌──────────────────────────────────────────────────────────┐
│  Software Update                           [Check Now]   │
├──────────────────────────────────────────────────────────┤
│                                                          │
│  3 update(s) available              Total: 15 MB         │
│                                                          │
│  ┌────────────────────────────────────────────────────┐  │
│  │ [x] simpleos-kernel    1.2.0 → 1.3.0      4 MB   │  │
│  │ [x] simpleos-core      1.2.0 → 1.3.0      8 MB   │  │
│  │ [x] simpleos-tools     1.0.0 → 1.1.0      3 MB   │  │
│  └────────────────────────────────────────────────────┘  │
│                                                          │
│  3 of 3 selected                      [Update Now]       │
│                                                          │
├──────────────────────────────────────────────────────────┤
│  Last checked: just now         [ ] Auto-check updates   │
└──────────────────────────────────────────────────────────┘
```

### States

| State | Display |
|-------|---------|
| Checking | Spinner + "Checking for updates..." |
| Up to date | Checkmark + "SimpleOS is up to date" |
| Updates ready | Package list + Update Now button |
| Downloading | Download progress bar |
| Installing | Per-package install progress + "Don't turn off" |
| Needs restart | Success + Restart Now / Later buttons |
| Failed | Error message + Try Again button |

## Keyboard Shortcuts

### Package Manager
| Key | Action |
|-----|--------|
| 1/2/3 | Switch tab (Installed/Available/Updates) |
| ↑/↓ | Navigate package list |
| i | Install selected |
| r | Remove selected |
| u | Update selected |
| U | Update all |
| c | Cycle category filter |
| y/n | Confirm/cancel dialog |
| Esc | Clear/close |

### Installer
| Key | Action |
|-----|--------|
| Enter | Next step |
| Esc | Previous step |
| ↑/↓ | Select disk |
| a | Accept license |

### Software Update
| Key | Action |
|-----|--------|
| c | Check for updates |
| u | Start update |
| r | Restart |
| a | Toggle auto-update |

## File Map

| File | Purpose | Lines |
|------|---------|-------|
| `src/os/tools/pkg/pkg_core.spl` | Shared package operations | ~250 |
| `src/os/apps/package_manager/package_manager.spl` | GUI package manager | ~300 |
| `src/os/apps/installer_gui/installer_gui.spl` | GUI installer wizard | ~400 |
| `src/os/apps/installer_gui/install_dialog.spl` | Install/remove dialogs | ~250 |
| `src/os/apps/installer_gui/upgrade_gui.spl` | Software update GUI | ~350 |
| `src/os/apps/installer_gui/mod.spl` | Module root | ~10 |
