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

The compiler supports multiple code generation backends. Selection is automatic based on build mode and available tools.

| Build Mode | Default Backend | Rationale |
|------------|----------------|-----------|
| Debug (`build`) | Cranelift | Fast compile times (~2.5x faster than LLVM) |
| Release (`build --release`) | LLVM-lib | Best runtime performance (4-5x faster code) |
| Explicit (`--backend=X`) | User choice | No auto-selection |

**Fallback chain for release builds:** `llvm-lib` (if `libLLVM` available) -> `llvm` (if `llc` available) -> `cranelift`.

### Platform Notes

- **Linux:** LLVM most commonly available. Install `libllvm-18-dev` for `llvm-lib` backend. Preferred linker: `mold`.
- **macOS:** Needs Homebrew LLVM (`brew install llvm`) for LLVM backend. Without it, all builds use Cranelift. Linker: system `ld` (ld64).
- **Windows:** LLVM rarely available; typically falls back to Cranelift. Supports both MSVC and MinGW toolchains.

---

## Bootstrap from Source

The Simple compiler is self-hosted. To build from scratch, a bootstrap process produces the first binary, which then compiles itself.

### Bootstrap Stages

```
Stage 1: Rust Seed Binary
  cargo build --profile bootstrap -p simple-driver
  -> src/compiler_rust/target/bootstrap/simple
  -> Backend: Cranelift (hardcoded)

Stage 2: Pure Simple (compiled by Stage 1)
  simple native-build
  -> bin/release/simple
  -> Backend: Cranelift

Stage 3: Self-Hosted (compiled by Stage 2)
  bin/release/simple build --release
  -> bin/release/simple
  -> Backend: auto (LLVM-lib > llc > Cranelift)
```

### Quick Bootstrap

```bash
# Automatic: download release binary, fall back to C bootstrap
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Download release binary only
scripts/bootstrap/download-release.sh --output=bin/release/simple

# Force C bootstrap (skip download)
scripts/bootstrap/bootstrap-from-scratch.sh --skip-download --deploy

# Pin to specific version
scripts/bootstrap/bootstrap-from-scratch.sh --download-version=0.7.0 --deploy
```

### Bootstrap Flags

| Flag | Description |
|------|-------------|
| `--deploy` | Copy result to `bin/release/simple` |
| `--skip-download` | Skip release download, force C bootstrap |
| `--download-version=X.Y.Z` | Pin to specific release version |
| `--keep-artifacts` | Keep `build/` directory |
| `--step=full2` | Run self-host verification |
| `--jobs=N` | Parallel build jobs (default: 7) |

### C Backend Bootstrap (Fallback)

When no pre-built binary is available, the C backend emits C++20 from the compiler source and builds with CMake + Ninja + Clang:

```bash
# Generate C++20 from compiler source
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl

# Build with CMake + Ninja
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build

# Install bootstrap binary
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple

# Self-host verification
bin/bootstrap/cpp/simple build
```

### Bootstrap Scripts

| Script | Purpose |
|--------|---------|
| `scripts/bootstrap/download-release.sh` | Download release binary from GitHub |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | Full bootstrap (download + C fallback) |
| `scripts/bootstrap/bootstrap-c.sh` | C backend bootstrap only |

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
| Production binary | `bin/release/simple` | Self-sufficient compiler/interpreter |
| C bootstrap | `bin/bootstrap/cpp/simple` | Built from generated C++20 |
| Build artifacts | `build/` | Intermediate files (safe to delete) |

The production binary (`bin/release/simple`) is fully self-sufficient. All compilation, interpretation, and test running happens in-process. The only external tool calls are to system compilers and linkers (`clang`, `gcc`, `mold`/`lld`/`ld`, `llc`).

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
