# Multi-Platform Bootstrap

Updated: 2026-03-22

## Target Triple Convention

Bootstrap artifacts use `<arch>-<vendor>-<os>-<abi>` target triples for platform directories, consistent with `LlvmTargetTriple` and `TargetPreset` in the compiler.

```
build/bootstrap/
  stage1/<triple>/simple(.exe)
  stage2/<triple>/simple(.exe)
  stage3/<triple>/simple(.exe)
```

### Field Definitions

| Field | Description | Values |
|-------|-------------|--------|
| **arch** | CPU architecture | `x86_64`, `aarch64`, `i686`, `riscv64` |
| **vendor** | Toolchain vendor | `pc` (Windows), `unknown` (Linux/FreeBSD), `apple` (macOS) |
| **os** | Operating system | `windows`, `linux`, `freebsd`, `darwin` |
| **abi** | ABI / object format | `msvc`, `gnu`, `elf`, `macho`, `eabihf` |

### Platform Triples

| Platform | Triple | ABI | Object Format |
|----------|--------|-----|---------------|
| Windows MSVC | `x86_64-pc-windows-msvc` | MSVC CRT | PE/COFF |
| Windows MinGW | `x86_64-pc-windows-gnu` | GNU CRT | PE/COFF |
| Linux x86_64 | `x86_64-unknown-linux-gnu` | GNU libc | ELF |
| FreeBSD x86_64 | `x86_64-unknown-freebsd-elf` | BSD libc | ELF |
| macOS ARM64 | `aarch64-apple-darwin-macho` | libSystem | Mach-O |
| macOS x86_64 | `x86_64-apple-darwin-macho` | libSystem | Mach-O |

### Comparison with Toolchain Conventions

| Toolchain | Windows MSVC | Windows MinGW | Linux |
|-----------|-------------|---------------|-------|
| **GCC** | n/a | `x86_64-w64-mingw32` | `x86_64-linux-gnu` |
| **Clang/LLVM** | `x86_64-pc-windows-msvc` | `x86_64-w64-mingw32` | `x86_64-unknown-linux-gnu` |
| **Rust** | `x86_64-pc-windows-msvc` | `x86_64-pc-windows-gnu` | `x86_64-unknown-linux-gnu` |
| **Simple** | `x86_64-pc-windows-msvc` | `x86_64-pc-windows-gnu` | `x86_64-unknown-linux-gnu` |

Simple follows Rust's convention for Windows (both MSVC and MinGW use `pc` vendor). For FreeBSD and macOS, Simple adds an explicit ABI field (`elf`, `macho`) where Rust and Clang omit it, ensuring all triples are consistently 4-part.

## Scope

The supported bootstrap levels are:

1. Stage 1: Rust-base Simple
2. Stage 2: pure Simple with `llvm-lib`
3. Stage 3: full pure-Simple self-host

The target host matrix is:

| Platform | Triple | Status |
|----------|--------|--------|
| Linux x86_64 | `x86_64-unknown-linux-gnu` | Active |
| FreeBSD x86_64 | `x86_64-unknown-freebsd-elf` | Active (QEMU guest) |
| macOS arm64 | `aarch64-apple-darwin-macho` | Prepared |
| macOS x86_64 | `x86_64-apple-darwin-macho` | Prepared |
| Windows MSVC | `x86_64-pc-windows-msvc` | Prepared |
| Windows MinGW | `x86_64-pc-windows-gnu` | Prepared |

## Canonical Commands

### Linux native

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap
```

Output:

```
build/bootstrap/stage1/x86_64-unknown-linux-gnu/simple
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
```

Wrapper behavior:

- builds the Rust seed compiler if needed
- detects platform triple from `uname -s` and `uname -m`
- runs `bin/simple build bootstrap`
- verifies Stage 2 and Stage 3 hashes
- optionally deploys the verified Stage 3 binary with `--deploy`

### FreeBSD via QEMU

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --output=build/bootstrap
```

Output:

```
build/bootstrap/stage1/x86_64-unknown-freebsd-elf/simple
build/bootstrap/stage2/x86_64-unknown-freebsd-elf/simple
build/bootstrap/stage3/x86_64-unknown-freebsd-elf/simple
```

Current note:

- the document history still mentions a QEMU wrapper script, but that script is not present in this checkout
- keep FreeBSD status as prepared until the repo-side entrypoint is restored or replaced

### Windows

```bash
scripts/bootstrap/bootstrap-windows.sh --output=build/bootstrap
```

Auto-detects MSVC vs MinGW. Force with `--msvc` or `--mingw`.

Output (MSVC):

```
build/bootstrap/stage1/x86_64-pc-windows-msvc/simple.exe
build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe
build/bootstrap/stage3/x86_64-pc-windows-msvc/simple.exe
```

Output (MinGW):

```
build/bootstrap/stage1/x86_64-pc-windows-gnu/simple.exe
build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe
build/bootstrap/stage3/x86_64-pc-windows-gnu/simple.exe
```

### Windows platform detection

Detection priority (in `bootstrap-windows.sh`):

1. `--msvc` / `--mingw` flags (forced)
2. `MSYSTEM` env var — `MINGW*` → mingw
3. `cl.exe` available → msvc
4. `clang-cl` available → msvc
5. `gcc` available → mingw
6. Default → msvc

Architecture detection uses `PROCESSOR_ARCHITECTURE` env var:

| Value | Arch |
|-------|------|
| `AMD64` / `x64` | `x86_64` |
| `ARM64` | `aarch64` |
| `x86` | `i686` |

## Platform Preparation

### Linux

Required:

- GCC or Clang toolchain
- LLVM development libraries for `llvm-lib` backend

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
- `sha256(stage2) == sha256(stage3)`
- final binary passes:
  - `--version`
  - `--help`
  - native hello-world compile and run

## Setup Script

After bootstrap or cloning a repo with pre-built release binaries, run the setup script to create the `bin/simple` symlink:

```bash
# Linux / macOS / Git Bash
scripts/setup.sh

# Windows CMD / PowerShell
scripts\setup.cmd
```

The setup script:

1. Auto-detects the platform triple (`<arch>-<vendor>-<os>-<abi>`)
2. Locates the release binary in `bin/release/<triple>/simple(.exe)` (falls back to legacy `bin/release/<os>-<arch>/` or the old flat layout)
3. Creates `bin/simple(.exe)` as a symlink (or hardlink/copy on Windows without developer mode)

Options:

| Flag | Description |
|------|-------------|
| `--triple=<T>` | Override auto-detected triple |
| `--msvc` / `--mingw` | Force ABI on Windows (setup.cmd) |
| `--dry-run` | Preview without creating links |

## Current Status

### Linux

- full 3-stage bootstrap is working
- Stage 2 and Stage 3 hashes match

### FreeBSD

- historical QEMU/bootstrap documentation exists
- executable wrapper script is not present in this checkout
- validation is still pending repo-side command restoration

### macOS and Windows

- toolchain assumptions are documented
- Windows bootstrap script updated with platform-aware directory layout
- final validation is still pending host-specific execution
