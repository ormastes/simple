# Build System

This guide covers the Simple build system, project configuration, build commands, and the bootstrap process for building Simple from source.

---

## Overview

The Simple language build system is fully self-hosted, written in Simple and configured with SDN (Simple Data Notation).

| Command | Description |
|---------|-------------|
| `bin/simple build` | Build the project |
| `bin/simple build --release` | Optimized release build |
| `bin/simple task <task>` | Run development tasks |
| `bin/simple watch` | Watch for file changes and rebuild |

---

## Project Configuration: `simple.sdn`

All project configuration uses SDN format:

```sdn
project:
    name: Simple
    version: 0.1.0

targets:
    formatter:
        source: src/app/formatter/main.spl
        output: bin/simple_fmt
        build_dir: build/formatter

    linter:
        source: src/app/lint/main.spl
        output: bin/simple_lint
        build_dir: build/lint
```

---

## Build Commands

```bash
# Build all targets
bin/simple build

# Build specific target
bin/simple build --target=formatter

# Release build (uses LLVM when available, otherwise Cranelift)
bin/simple build --release

# Clean build artifacts
bin/simple build --clean

# Verbose output
bin/simple build --verbose
```

### Quality Commands

```bash
bin/simple build fmt            # Format all .spl files
bin/simple build lint           # Run linter
bin/simple build check          # Format + lint + test
```

---

## Task Runner

Run common development tasks with dependency resolution:

```bash
bin/simple task --list          # List all tasks
bin/simple task build           # Build all tools
bin/simple task test            # Run all tests
bin/simple task dev             # Build + unit tests
bin/simple task ci              # Format + lint + test + coverage
```

| Task | Description | Dependencies |
|------|-------------|--------------|
| `build` | Build all tools | -- |
| `test` | Run all tests | -- |
| `test-unit` | Unit tests only | -- |
| `test-system` | System tests only | -- |
| `fmt` | Format all .spl files | build |
| `lint` | Lint all .spl files | build |
| `check` | Format + lint + test | fmt, lint, test |
| `clean` | Clean build artifacts | -- |
| `dev` | Quick dev build | build, test-unit |
| `ci` | Full CI check | fmt, lint, test, coverage |

---

## Watch Mode

Automatically rebuild on file changes:

```bash
bin/simple watch                    # Watch and build
bin/simple watch --task=test        # Watch and run tests
bin/simple watch --debounce=1000    # Custom debounce (ms)
```

---

## Backend Selection

The compiler supports multiple code generation backends:

| Mode | Default Backend | Rationale |
|------|----------------|-----------|
| Interpreter / Loader | Cranelift | Fast JIT compilation for running and loading code |
| Compiler (`build`, `native-build`) | LLVM | Optimized native binary output |
| Explicit (`--backend=X`) | User choice | No auto-selection |

**Fallback chain for compiler builds:** `llvm-lib` (if `libLLVM` available) -> `llvm` (if `llc` available) -> `cranelift`.

### Platform Notes

- **Linux:** LLVM most commonly available. Install `libllvm-18-dev` for `llvm-lib` backend. Preferred linker: `mold`.
- **macOS:** Needs Homebrew LLVM (`brew install llvm`) for LLVM backend. Without it, all builds use Cranelift. Linker: system `ld` (ld64).
- **Windows:** LLVM rarely available; typically falls back to Cranelift. Supports both MSVC and MinGW toolchains.

### SimpleOS Multi-Platform Binaries

SimpleOS target metadata is centralized in `src/os/port/simpleos_multiplatform_build.spl`. The catalog lists the Simple entrypoint, linker script, QEMU binary, freestanding C flags, assembly flags, and boot support sources for each OS target.

```bash
# Build all first-class SimpleOS QEMU targets
bin/simple run examples/simple_os/build.spl

# Build 32-bit x86 explicitly
bin/simple run examples/simple_os/build.spl -- --arch=x86_32
bin/simple run examples/simple_os/build.spl -- --arch=i686
```

The 32-bit x86 lane is `i686-simpleos`: C boot support is compiled with `--target=i686-unknown-none-elf -m32`, assembly boot support uses the same i686 freestanding target, QEMU runs with `qemu-system-i386`, and the SimpleOS runner defaults that lane to LLVM because Cranelift does not expose an i686 freestanding target here. Build the selected compiler binary with the Rust `llvm` feature and LLVM 18 available through `LLVM_SYS_180_PREFIX` or system discovery before using this lane.

---

## Bootstrap from Source

The Simple compiler is self-hosted. To build from scratch, a bootstrap process produces the first binary, which then compiles itself.

### Bootstrap Stages

```
Stage 1: Rust Seed Binary
  cargo build --profile bootstrap -p simple-driver
  -> src/compiler_rust/target/bootstrap/simple
  -> Backend: Cranelift (hardcoded)

Stage 2: Pure Simple (compiled by Rust seed)
  seed native-build --entry bootstrap_main.spl
  -> build/bootstrap/stage2/<triple>/simple
  -> Backend: llvm-lib (default)

Stage 3: Self-Hosted (compiled by Stage 2)
  stage2 native-build --entry bootstrap_main.spl
  -> build/bootstrap/stage3/<triple>/simple
  -> Backend: llvm-lib (default)

Stage 4: Full CLI (compiled by verified stage)
  stage3 native-build --entry main.spl
  -> build/bootstrap/full/<triple>/simple
  -> Backend: llvm-lib (default)
```

### Quick Bootstrap

```bash
# Linux / macOS (same script, auto-detects platform)
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Windows (Git Bash / MSYS2)
scripts/bootstrap/bootstrap-windows.sh --deploy

# Keep artifacts in a separate directory
scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap
```

The `--deploy` flag copies the final binary to `bin/release/<triple>/simple` and runs `scripts/setup.sh` automatically to regenerate the `bin/simple` wrapper and related launchers.

Bootstrap output uses `<arch>-<vendor>-<os>-<abi>` target triples:

```
build/bootstrap/stage2/<triple>/simple
build/bootstrap/stage3/<triple>/simple
build/bootstrap/full/<triple>/simple

# Examples:
#   x86_64-unknown-linux-gnu
#   aarch64-apple-darwin-macho
#   x86_64-pc-windows-msvc
```

### Bootstrap Flags

| Flag | Description |
|------|-------------|
| `--deploy` | Copy result to `bin/release/<triple>/simple` and run `setup.sh` |
| `--backend=X` | Override bootstrap backend (`llvm-lib` by default) |
| `--output=DIR` | Write stage outputs to a custom directory |
| `--keep-artifacts` | Keep `build/` directory |
| `--no-verify` | Compatibility flag; wrapper still verifies stage hashes |

### Bootstrap Scripts

| Script | Purpose |
|--------|---------|
| `scripts/setup.sh` | Post-bootstrap setup — creates `bin/simple` symlink |
| `scripts/setup.cmd` | Windows CMD/PowerShell equivalent |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | Verified staged Linux/macOS/FreeBSD bootstrap |
| `scripts/bootstrap/bootstrap-windows.sh` | Windows bootstrap (MSVC / MinGW auto-detect) |

---

## Building from Source (Prerequisites)

### Required Tools

- **Rust** 1.75+ (for Stage 1 seed) -- install from [rustup.rs](https://rustup.rs)
- **clang** 14+ (C11 support)
- **cmake** 3.20+
- **Git**

Platform-specific build tools:
- **Linux:** `build-essential` (Ubuntu/Debian) or `base-devel` (Arch)
- **macOS:** Xcode Command Line Tools (`xcode-select --install`)
- **Windows:** Visual Studio Build Tools

### Verify Tools

```bash
clang --version     # 14+
cmake --version     # 3.20+
rustc --version     # 1.75+
```

---

## Build Output

| Artifact | Path | Description |
|----------|------|-------------|
| Entry point | `bin/simple` | Symlink → `release/<triple>/simple` |
| Platform binary | `bin/release/<triple>/simple` | Self-sufficient compiler/interpreter |
| Build artifacts | `build/` | Intermediate files (safe to delete) |

The platform binary is fully self-sufficient. All compilation, interpretation, and test running happens in-process. The only external tool calls are to system compilers and linkers (`clang`, `gcc`, `mold`/`lld`/`ld`, `llc`). The `scripts/setup.sh` script creates the `bin/simple` symlink pointing to the correct platform binary.

---

## Example Workflows

### Daily Development

```bash
bin/simple watch                # Auto-rebuild on changes
bin/simple test                 # Run tests in another terminal
```

### Before Commit

```bash
bin/simple task check           # Format + lint + test
```

### CI Pipeline

```bash
bin/simple task ci              # Full CI check
```

---

## See Also

- [CLI Reference](cli.md) -- command-line arguments and subcommands
- [Getting Started](getting_started.md) -- installation and first program
