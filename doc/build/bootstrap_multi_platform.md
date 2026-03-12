# Multi-Platform Bootstrap

Updated: 2026-03-12

This document tracks the executable bootstrap flow that matches the root plan in [plan_codex_bootstrap.md](/home/ormastes/dev/pub/simple/plan_codex_bootstrap.md).

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
scripts/bootstrap/bootstrap-from-scratch.sh --output=bootstrap
```

Verified on Linux x86_64 on 2026-03-12:

- exit code `0`
- `bootstrap/simple_stage1` produced
- `bootstrap/simple_stage2` produced
- `bootstrap/simple_stage3` produced
- `sha256(bootstrap/simple_stage2) == sha256(bootstrap/simple_stage3)`

Wrapper behavior:

- builds the Rust seed compiler if needed
- runs `bin/release/simple build bootstrap`
- verifies Stage 2 and Stage 3 hashes
- optionally deploys the verified Stage 3 binary with `--deploy`

Artifacts:

- `bootstrap/simple_stage1`
- `bootstrap/simple_stage2`
- `bootstrap/simple_stage3`
- existing runtime/compiler entrypoint remains `bin/release/simple`

### FreeBSD via QEMU

```bash
bin/release/simple build pipeline --from=seed --to=full2
```

Current note:

- the document history still mentions a QEMU wrapper script, but that script is not present in this checkout
- keep FreeBSD status as prepared until the repo-side entrypoint is restored or replaced

Host-side outputs:

- `bin/release/simple`
- `build/freebsd/bootstrap/stage1/simple`
- `build/freebsd/bootstrap/stage2/simple`
- `build/freebsd/bootstrap/stage3/simple`

### Windows

Use the same staged build flow once the Windows wrapper is restored.

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

Expected LLVM locations:

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

- full 3-stage bootstrap is working in this checkout
- Stage 2 and Stage 3 hashes match
- remaining work is documentation cleanup and restoring non-Linux wrapper scripts if they are still desired

### FreeBSD

- historical QEMU/bootstrap documentation exists
- executable wrapper script is not present in this checkout
- validation is still pending repo-side command restoration

### macOS and Windows

- toolchain assumptions are documented
- final validation is still pending host-specific entrypoint restoration and execution
