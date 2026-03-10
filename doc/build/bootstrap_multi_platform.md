# Multi-Platform Bootstrap

Updated: 2026-03-10

This document tracks the executable bootstrap flow that matches the root plan in `plan_codex_bootstrap.md`.

## Scope

The supported bootstrap levels are:

1. Stage 1: Rust-base Simple
2. Stage 2: pure Simple with `llvm-lib`
3. Stage 3: full pure-Simple self-host

The target host matrix is:

| Platform | Status | Execution mode |
|----------|--------|----------------|
| Linux x86_64 | Active | Native |
| FreeBSD x86_64 | Active | QEMU guest from Linux host |
| macOS arm64/x86_64 | Prepared | Native host or CI later |
| Windows x86_64 MinGW | Prepared | Native host or CI later |
| Windows x86_64 MSVC | Prepared | Native host or CI later |

## Canonical Commands

### Linux native

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --keep-artifacts --deploy
```

The shell bootstrap script now uses:

- `src/app/cli/main.spl` for Stage 1
- `--backend llvm-lib` for Stage 2
- `--backend llvm-lib` for Stage 3
- `--clean` on each stage boundary

Artifacts:

- `build/bootstrap/stage1/simple`
- `build/bootstrap/stage2/simple`
- `build/bootstrap/stage3/simple`
- `bin/release/simple`

### FreeBSD via QEMU

```bash
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --deploy
```

The QEMU wrapper:

- starts or reuses the FreeBSD guest
- syncs the repo into `~/simple`
- runs the shared bootstrap script inside the guest
- copies back `bin/release/simple`
- copies back `build/bootstrap` into `build/freebsd/bootstrap`

Host-side outputs:

- `bin/release/simple`
- `build/freebsd/bootstrap/stage1/simple`
- `build/freebsd/bootstrap/stage2/simple`
- `build/freebsd/bootstrap/stage3/simple`

### Windows

```bat
scripts\bootstrap\bootstrap-from-scratch.bat --deploy
```

The batch bootstrap entry is prepared for both Windows lanes:

- MinGW or MSYS2 environments with LLVM available
- MSVC environments where `clang-cl` and Visual Studio tooling are on `PATH`

It follows the same three-stage contract and uses `src\app\cli\main.spl`.

## Platform Preparation

### macOS

Required:

- Xcode Command Line Tools
- clang toolchain
- Homebrew or equivalent LLVM installation for `llvm-lib`

Expected LLVM locations already handled in scripts:

- `/opt/homebrew/opt/llvm/lib`
- `/usr/local/opt/llvm/lib`
- versioned Homebrew LLVM prefixes

### Windows MinGW

Required:

- MSYS2 with `mingw64`, `clang64`, or `ucrt64`
- LLVM `LLVM-C.dll`
- `clang`, `gcc`, or `clang-cl`

### Windows MSVC

Required:

- Visual Studio Build Tools
- `link.exe` or `lld-link.exe`
- LLVM install exposing `LLVM-C.dll`

Keep MinGW and MSVC as separate validation lanes. Do not treat one as proof for the other.

## Success Criteria

Each platform is only green when:

- Stage 1 builds the full CLI
- Stage 2 builds from Stage 1 with `llvm-lib`
- Stage 3 rebuilds from Stage 2 with `llvm-lib`
- final binary passes:
  - `--version`
  - `--help`
  - native hello-world compile and run

Additional Linux and FreeBSD requirement:

- Stage 2 and Stage 3 hashes are compared and any mismatch is explained

## Current Status

### Linux

- Stage 1 full CLI bootstrap is working
- Stage 2 is still blocked in the pure-Simple frontend/runtime path

### FreeBSD

- QEMU execution path and artifact retrieval are wired
- validation depends on the same Stage 2 pure-Simple unblock

### macOS and Windows

- scripts and toolchain assumptions are prepared
- final validation is pending after the Linux Stage 2 unblock
