# SimpleOS Development Environment Guide

Version: 1.0.0  
Date: 2026-04-06  
Status: Active

## Overview

SimpleOS is a multi-architecture operating system written in Simple. This guide covers the full development environment: shell tools, version control, build systems, toolchain deployment, and compiler bootstrap.

All verification can be run with a single command:

```bash
bin/simple run src/os/port/verify_all.spl
```

---

## Table of Contents

1. [Shell (sosh)](#1-shell-sosh)
2. [Version Control (git, jj, vcs)](#2-version-control)
3. [Build Tools (make, cmake, ninja)](#3-build-tools)
4. [Toolchain Deployment (LLVM, Rust)](#4-toolchain-deployment)
5. [Simple Compiler Bootstrap](#5-simple-compiler-bootstrap)
6. [Verification Script](#6-verification-script)
7. [Architecture Reference](#7-architecture-reference)

---

## 1. Shell (sosh)

**Source:** `src/os/apps/shell/`  
**Binary name:** `sosh` (SimpleOS Shell v0.2)

### 1.1 Core Built-in Commands (26)

| Category | Commands |
|----------|----------|
| **Filesystem** | `cd`, `ls [-a] [-l]`, `pwd`, `cat`, `mkdir`, `rm`, `cp`, `mv` |
| **Search** | `grep PATTERN FILE...`, `find DIR [-name PATTERN]` |
| **Process** | `ps`, `kill [-SIGNAL] PID` |
| **System** | `mount [DEV PATH [TYPE]]`, `hostname`, `uptime`, `dmesg [N]` |
| **Environment** | `env`, `export KEY=VALUE`, `history`, `echo` |
| **Job Control** | `jobs`, `fg [ID]`, `bg [ID]`, `CMD &` |
| **File Access** | `readf [--async] FILE` |
| **Shell** | `clear`, `help`, `exit` |

### 1.2 Extended Tools (14)

Located in `src/os/apps/shell/shell_tools.spl`:

| Command | Description |
|---------|-------------|
| `touch FILE...` | Create empty files or update timestamps |
| `head [-n N] FILE` | Show first N lines (default 10) |
| `tail [-n N] FILE` | Show last N lines (default 10) |
| `wc [-l] [-w] [-c] FILE...` | Word/line/char count |
| `sort FILE` | Sort lines alphabetically |
| `uniq FILE` | Remove consecutive duplicate lines |
| `which CMD` | Show which tool/builtin handles command |
| `date` | Show current date/time |
| `true` / `false` | Exit 0 / Exit 1 |
| `tee FILE` | Write stdin to stdout and file |
| `ln -s TARGET LINK` | Create symlink |
| `chmod MODE FILE` | File permissions (stub — VFS has no perms yet) |
| `stat FILE` | Show file info (size, type) |

### 1.3 Shell Features

- **Pipelines:** `cmd1 | cmd2 | cmd3` — POSIX pipes with fd redirection
- **Redirections:** `>`, `>>`, `<`, `2>`, `2>>` — save/restore fd around commands
- **Background:** `CMD &` — job table with `fg`/`bg`/`jobs`
- **Quoting:** single quotes, double quotes, backslash escaping
- **Variable expansion:** `$VAR` in `echo` and arguments
- **External commands:** dispatched to ToolRegistry or spawned as child processes

### 1.4 Tool Registry

External tools register via `ToolRegistry` (`src/os/tools/tool_registry.spl`):

| Category | Tools |
|----------|-------|
| `proc/` | ps, top, kill, nice |
| `net/` | ping, ifconfig, netstat, wget, dns, dhcp |
| `boot/` | boot_manager, boot_recovery |
| `log/` | journal, log_viewer |
| `dev/` | devinfo, lspci, lsblk, lsusb |
| `pkg/` | pkg_manager, pkg_resolver, pkg_manifest, pkg_repository |
| `archive/` | tar, gzip, zip |

### 1.5 Adding a New Shell Command

1. Add `fn tool_mycommand(vfs, cwd, args, terminal) -> i32` to `shell_tools.spl`
2. Add `"mycommand": self.cmd_mycommand(args)` to `_dispatch_builtin` in `shell_app.spl`
3. Add `cmd_mycommand` method that delegates to `tool_mycommand`
4. Add to `_execute_background` builtins list and `cmd_help` output

---

## 2. Version Control

SimpleOS provides three VCS options: native VCS, git wrapper, and jj wrapper.

### 2.1 Native VCS

**Source:** `src/os/apps/vcs/vcs_app.spl`  
**Shell command:** `vcs`

A lightweight file-level snapshot VCS built for SimpleOS:

```bash
vcs init                    # Initialize .vcs/ repository
vcs add file1.spl file2.spl  # Stage files
vcs commit -m "message"     # Create snapshot
vcs log                     # Show commit history
vcs status                  # Show staged/modified files
vcs diff [file]             # Line-by-line diff vs HEAD
vcs checkout <hash>         # Restore files from a commit
vcs show <hash>             # Show commit details
```

Storage: `.vcs/` directory with djb2 hashes (8 hex chars). Linear history only — no branches or merge.

### 2.2 Git Wrapper

**Source:** `src/os/apps/git/git_app.spl`  
**Shell command:** `git`

Delegates to the host `git` binary via `rt_process_run`. All standard git commands are supported:

```bash
git init                    # Initialize .git repository
git clone URL [DIR]         # Clone repository
git add FILE...             # Stage files
git commit -m "message"     # Create commit
git status                  # Show working tree status
git log [--oneline] [-n N]  # Show history
git diff [FILE]             # Show diff
git branch [-a] [NAME]      # List/create branches
git checkout BRANCH         # Switch branch
git merge BRANCH            # Merge branch
git push [REMOTE] [BRANCH]  # Push to remote
git pull [--rebase]         # Pull from remote
git remote [-v] [add ...]   # Manage remotes
git stash [pop]             # Stash changes
```

Unrecognized subcommands pass through directly to git.

### 2.3 JJ (Jujutsu) Wrapper

**Source:** `src/os/apps/jj/jj_app.spl`  
**Shell command:** `jj`

Delegates to the host `jj` binary. Log uses `--no-pager` by default:

```bash
jj init                     # Initialize jj repository
jj log                      # Show revision log
jj status / jj st           # Show working copy status
jj diff                     # Show current change diff
jj new                      # Create new change
jj describe -m "message"    # Describe current change
jj commit -m "message"      # Commit current change
jj bookmark set NAME [-r R] # Set bookmark
jj git push                 # Push to remote
jj git fetch                # Fetch from remote
jj rebase -d DEST           # Rebase onto destination
jj squash                   # Squash into parent
jj abandon                  # Abandon current change
```

---

## 3. Build Tools

### 3.1 simple_make (In-Tree)

**Source:** `src/os/port/build_tools/simple_make.spl`

A make-compatible build tool designed to run ON SimpleOS:

```bash
bin/simple run src/os/port/build_tools/simple_make.spl
bin/simple run src/os/port/build_tools/simple_make.spl -- -f build.mk
bin/simple run src/os/port/build_tools/simple_make.spl -- clean
```

Supported features:
- Variable assignment (`VAR = value`) and `$(VAR)` expansion
- Pattern rules (`%.o: %.c`)
- Automatic variables (`$@`, `$<`, `$^`)
- Dependency-based rebuild via mtime comparison
- CLI: `-f FILE`, target selection

Not yet: parallel builds (`-j N`), conditionals, `include`, `.PHONY`.

### 3.2 CMake Port (examples/cmake/)

**Source:** `examples/cmake/`

SimpleOS-native CMakeLists.txt parser and build file generator:

```bash
bin/simple run examples/cmake/simple_cmake.spl -- examples/cmake/example/
```

Supported CMake subset:
- `cmake_minimum_required`, `project`, `add_executable`, `add_library`
- `target_link_libraries`, `target_include_directories`
- `set()` / `${VAR}`, `if()/else()/endif()`
- `message()`, `option()`, `find_program()`, `find_library()`
- Generates Makefile or build.ninja output

### 3.3 Ninja Port (examples/ninja/)

**Source:** `examples/ninja/`

Ninja build file parser and executor:

```bash
bin/simple run examples/ninja/simple_ninja.spl -- examples/ninja/example/
```

Supported ninja subset:
- `rule NAME` with `command`, `description`, `depfile`
- `build OUTPUT: RULE INPUT...` with implicit and order-only deps
- Variable declarations and `$var` expansion
- `pool`, `default`, `include`, `subninja`
- Dependency-based rebuild, parallel execution

### 3.4 Enhanced Make (examples/make/)

**Source:** `examples/make/`

Enhanced make implementation beyond simple_make:

```bash
bin/simple run examples/make/simple_make_enhanced.spl -- -j4 all
```

Additional features over simple_make:
- `.PHONY` targets
- `include`, `ifeq`/`ifdef` conditionals
- `$(shell CMD)`, `$(wildcard)`, `$(patsubst)`, `$(foreach)`, `$(filter)`
- `-j N` parallel builds
- `VPATH`/`vpath`, `$(MAKE)` recursive
- `--dry-run`, colored output

---

## 4. Toolchain Deployment

### 4.1 Quick Start

```bash
# Deploy all toolchains (sysroot + LLVM + Rust + tests)
bin/simple run src/os/port/deploy_toolchains.spl

# Just check current status
bin/simple run src/os/port/deploy_toolchains.spl -- --status

# Build specific stage
bin/simple run src/os/port/deploy_toolchains.spl -- --stage sysroot
bin/simple run src/os/port/deploy_toolchains.spl -- --stage llvm
bin/simple run src/os/port/deploy_toolchains.spl -- --stage rust
bin/simple run src/os/port/deploy_toolchains.spl -- --stage test

# Also build LLVM for self-hosting ON SimpleOS
bin/simple run src/os/port/deploy_toolchains.spl -- --cross
```

### 4.2 Supported Targets

| Target Triple | Architecture | Notes |
|--------------|-------------|-------|
| `x86_64-simpleos` | x86-64 | Primary, most tested |
| `aarch64-simpleos` | ARM64 | |
| `riscv64gc-simpleos` | RISC-V 64 | GC extensions |
| `riscv32imac-simpleos` | RISC-V 32 | IMAC extensions |

### 4.3 Sysroot Layout

Built by `src/os/port/llvm/sysroot.shs` into `build/os/sysroot/`:

```
build/os/sysroot/
  include/              # C headers (stdio.h, stdlib.h, string.h, math.h, ...)
  include/c++/          # Minimal C++ headers
  lib/                  # libsimpleos_c.a, crt0.o, compiler-rt builtins
  share/simpleos/       # simpleos.ld linker script
```

### 4.4 LLVM Cross-Build

**Source:** `src/os/port/llvm/`

The LLVM build script (`build.spl`) supports two modes:

1. **Host build** (default): Builds LLVM/Clang on host targeting SimpleOS
2. **Cross build** (`--cross`): 3-stage pipeline producing LLVM that runs ON SimpleOS
   - Stage 1: Build host tools (llvm-tblgen, clang-tblgen)
   - Stage 2: Cross-compile LLVM/Clang/LLD for SimpleOS
   - Stage 3: Cross-compile compiler-rt builtins

```bash
# Build for one target
bin/simple run src/os/port/llvm/build.spl -- --target x86_64-simpleos

# Build for all targets
bin/simple run src/os/port/llvm/build.spl -- --all

# Cross-build (LLVM running ON SimpleOS)
bin/simple run src/os/port/llvm/build.spl -- --cross --target x86_64-simpleos

# Check status
bin/simple run src/os/port/llvm/build.spl -- --status

# Run smoke tests
bin/simple run src/os/port/llvm/test_smoke.spl
```

Uses fork: `ormastes/llvm-project` (branch: `simpleos`)

### 4.5 Rust Cross-Build

**Source:** `src/os/port/rust/`

Builds Rust `core` and `alloc` crates for SimpleOS target:

```bash
# Build toolchain
bin/simple run src/os/port/rust/build.spl -- --target x86_64-simpleos

# Build examples
bin/simple run src/os/port/rust/build.spl -- examples

# Validate without Rust nightly
bin/simple run src/os/port/rust/build.spl -- validate
```

Target specs: `src/os/toolchain/rust/`
- `x86_64-unknown-simpleos.json`
- `aarch64-unknown-simpleos.json`
- `riscv64gc-unknown-simpleos.json`
- `riscv32imac-unknown-simpleos.json`

Uses fork: `ormastes/rust` (branch: `simpleos`)

### 4.6 SimpleOS Libc

**Source:** `src/os/libc/`

| File | Contents |
|------|----------|
| `simpleos_libc.c` | Core: syscalls, string ops, printf, mmap, file I/O |
| `simpleos_math.c` | Basic: fabs, fabsf, sqrt, sqrtf |
| `simpleos_string_ext.c` | Extended: strerror, strncat, memrchr, strlcpy, strlcat |
| `simpleos_math_ext.c` | Extended: scalbn, log1p, expm1 (for Rust core + LLVM) |
| `Makefile` | Builds `libsimpleos_c.a` |
| `include/` | C headers (string.h, math.h, stdio.h, ...) |

### 4.7 Native Build Config

**Source:** `src/os/port/simpleos_native_build_config.spl`

Provides configuration for `simple native-build --target simpleos`:

```simple
val config = simpleos_build_config("x86_64-simpleos")
val flags = simpleos_linker_flags()
val includes = simpleos_include_paths()
val valid = simpleos_validate_sysroot("build/os/sysroot")
```

Functions: `simpleos_sysroot_path()`, `simpleos_linker_flags()`, `simpleos_include_paths()`, `simpleos_target_arch()`, `simpleos_clang_target()`, `simpleos_c_flags()`, `simpleos_crt_objects()`, `simpleos_library_paths()`, `simpleos_libraries()`, `simpleos_linker_script()`, `simpleos_validate_sysroot()`.

---

## 5. Simple Compiler Bootstrap

### 5.1 Bootstrap Path

The Simple compiler bootstraps through 3 stages:

```
Host Rust seed ─→ Stage 1 ─→ Stage 2 ─→ Stage 3
     (Rust)        (Simple)    (Simple)    (Simple)
                                     ╰─ must equal Stage 2 (convergence)
```

On SimpleOS, an additional cross-compilation step produces the seed:

```
Host Rust seed ──cross-compile──→ SimpleOS Rust seed
SimpleOS Rust seed ─→ Stage 1 ─→ Stage 2 ─→ Stage 3
```

### 5.2 Verification Script

```bash
# Check all prerequisites (no build)
bin/simple run src/os/port/bootstrap_verify.spl -- --dry-run

# Run full 3-stage bootstrap
bin/simple run src/os/port/bootstrap_verify.spl

# Run up to stage 2 only
bin/simple run src/os/port/bootstrap_verify.spl -- --stage 2

# Use custom seed binary
bin/simple run src/os/port/bootstrap_verify.spl -- --seed /path/to/seed

# Verbose output
bin/simple run src/os/port/bootstrap_verify.spl -- --verbose
```

### 5.3 Cross-Compilation Bootstrap

Build the Simple compiler FOR SimpleOS from a host machine:

```bash
# Cross-compile for x86_64
bin/simple run src/os/port/bootstrap_cross.spl -- --target x86_64-simpleos

# Cross-compile for aarch64
bin/simple run src/os/port/bootstrap_cross.spl -- --target aarch64-simpleos

# Create deployable archive
bin/simple run src/os/port/bootstrap_cross.spl -- --target x86_64-simpleos --package

# Check build status for all targets
bin/simple run src/os/port/bootstrap_cross.spl -- --status
```

### 5.4 Full Bootstrap Plan

See `doc/03_plan/simpleos_bootstrap_plan.md` for the detailed 4-phase plan:
- Phase 0: Prerequisites
- Phase 1: Rust seed on SimpleOS
- Phase 2: Stage 1 on SimpleOS
- Phase 3: Stage 2 & 3 (self-hosting + convergence)
- Phase 4: Verification

---

## 6. Verification Script

### 6.1 Full Verification

```bash
# Run all 5 phases
bin/simple run src/os/port/verify_all.spl

# Verbose output
bin/simple run src/os/port/verify_all.spl -- --verbose

# Dry-run (check files only, no builds)
bin/simple run src/os/port/verify_all.spl -- --dry-run

# Skip slow phases (toolchain + bootstrap)
bin/simple run src/os/port/verify_all.spl -- --skip-slow
```

### 6.2 Individual Phases

```bash
bin/simple run src/os/port/verify_all.spl -- --phase shell
bin/simple run src/os/port/verify_all.spl -- --phase vcs
bin/simple run src/os/port/verify_all.spl -- --phase build-tools
bin/simple run src/os/port/verify_all.spl -- --phase toolchain
bin/simple run src/os/port/verify_all.spl -- --phase bootstrap
```

### 6.3 Phases

| Phase | Name | What It Checks |
|-------|------|----------------|
| 1 | `shell` | 26 core commands, 14 extended tools, features (pipes, redirects, bg) |
| 2 | `vcs` | Native VCS, git wrapper (15 cmds), jj wrapper (14 cmds), host tools |
| 3 | `build-tools` | simple_make, cmake/ninja/make ports, host tool availability |
| 4 | `toolchain` | LLVM/Rust build scripts, 4 target specs, libc, sysroot, smoke tests |
| 5 | `bootstrap` | Bootstrap scripts, Rust seed, entry points, source dirs, native config |

### 6.4 Example Output

```
SimpleOS Full Verification v1.0.0
Target: x86_64-simpleos

================================================================
  Phase 1: Shell Tools
================================================================

--- Core Shell Files ---
  [PASS] Shell app: src/os/apps/shell/shell_app.spl
  [PASS] Pipeline support: src/os/apps/shell/shell_pipe.spl
  ...

  shell: PASS  (48 passed, 0 failed, 0 skipped)

================================================================
  Final Summary
================================================================

  [PASS] shell            48 passed, 0 failed, 0 skipped
  [PASS] vcs              32 passed, 0 failed, 0 skipped
  [PASS] build-tools      18 passed, 0 failed, 0 skipped
  [PASS] toolchain        28 passed, 0 failed, 0 skipped
  [PASS] bootstrap        20 passed, 0 failed, 0 skipped

  Total: 146 checks -- 146 passed, 0 failed, 0 skipped
  Result: ALL PHASES PASSED
```

---

## 7. Architecture Reference

### 7.1 File Map

```
src/os/
  apps/shell/           # Shell (sosh): shell_app, shell_pipe, shell_redirect,
                        #   shell_job, shell_async, shell_tools
  apps/git/             # Git wrapper (git_app)
  apps/jj/              # JJ wrapper (jj_app)
  apps/vcs/             # Native VCS (vcs_app)
  tools/                # System tools: proc/, net/, boot/, log/, dev/, pkg/, archive/
  port/
    build_tools/        # simple_make
    llvm/               # LLVM cross-build (build.spl, sysroot.shs, test_smoke.spl)
    rust/               # Rust cross-build (build.spl, examples/)
    verify_all.spl      # Master verification script
    deploy_toolchains.spl  # Unified toolchain deployment
    bootstrap_verify.spl   # Bootstrap verification
    bootstrap_cross.spl    # Cross-compilation bootstrap
    simpleos_native_build_config.spl  # Build configuration
  toolchain/
    llvm/               # CMake toolchain file
    rust/               # Target specs (4 JSON) + cargo config
  libc/                 # Minimal C runtime (libc, math, string ext)
examples/
  cmake/                # CMake port
  ninja/                # Ninja port
  make/                 # Enhanced make port
doc/
  03_plan/simpleos_bootstrap_plan.md  # Full bootstrap plan
  05_design/os_dev_toolchain_porting.md  # Porting roadmap
  07_guide/platform/simpleos_dev_guide.md  # This guide
```

### 7.2 Dependencies

```
Shell Tools ──→ VfsManager, ToolRegistry, Terminal, POSIX layer
Git/JJ      ──→ rt_process_run (host binary delegation)
Build Tools ──→ std.fs, std.process (file ops + command execution)
LLVM Build  ──→ cmake, ninja, clang, git (host tools)
Rust Build  ──→ python3, git, rustup, cargo nightly, rust-src
Bootstrap   ──→ Rust seed, clang/lld (linking), source tree
Verify All  ──→ std.fs (file checks), std.process (tool checks)
```

### 7.3 Related Documentation

- [Porting Roadmap](../../../doc/05_design/os_dev_toolchain_porting.md)
- [Bootstrap Plan](../../../doc/03_plan/simpleos_bootstrap_plan.md)
- [LLVM Port README](../../../src/os/port/llvm/README.md)
- [Rust Port README](../../../src/os/port/rust/README.md)
- [GUI Port README](../../../src/os/port/gui/README.md)
- [Baremetal Guide](backend/baremetal.md)
- [Platform Guide](platforms.md)

---

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
| GUI Desktop | `examples/simple_os/arch/x86_64/gui_entry.spl` | Full desktop shell + all 28 apps |
| Glass WM | `examples/simple_os/arch/x86_64/wm_entry.spl` | Self-contained glass window manager |
| GPU Test | `examples/simple_os/arch/x86_64/gpu_test_entry.spl` | VirtIO-GPU testing |
| Minimal GUI | `examples/simple_os/arch/x86_64/gui_entry_minimal.spl` | Minimal framebuffer test |

### 8.7 QEMU Configuration

| Parameter | GUI Target | WM Target |
|-----------|-----------|-----------|
| Machine | q35 | q35 |
| CPU | qemu64 | qemu64 |
| Memory | 2G | 512M |
| Display | cocoa | cocoa |
| VGA | std (BGA) | std (BGA) |
| Resolution | 1024x768x32 | 1024x768x32 |

### 8.8 Known Issues

- **Cranelift non-determinism**: Clean rebuilds may produce different auto-stub patterns due to HashMap iteration order. Incremental builds are more reliable.
- **Heap exhaustion**: Bump allocator never frees. Long event loop sessions exhaust 512MB heap. Production fix: implement GC or arena allocator.
- **Serial garbling**: `serial_writeln` (Simple function) outputs garbled text (8x character repeat). Use `serial_println` (C extern) for clean output.
- **objcopy required**: QEMU Multiboot1 requires 32-bit ELF. Build produces 64-bit, needs `llvm-objcopy --output-target=elf32-i386` conversion.

### 8.9 Source Layout

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

examples/simple_os/
  arch/x86_64/    — x86_64 entry points, linker script, boot/ C stubs
  src/            — GUI kernel main
```
