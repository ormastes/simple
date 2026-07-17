# Build System

This guide covers the Simple build system, project configuration, build commands, and the bootstrap process for building Simple from source.

---

## Overview

The Simple language build system is fully self-hosted, written in Simple and configured with SDN (Simple Data Notation).

> **Default toolchain = pure-Simple, not the Rust seed.** All tooling
> (`test`, `lint`, `fmt`, `check`, `build`, `run`, `-c`, the MCP/LSP servers,
> doc-coverage) is expected to run on the **self-hosted** binary
> `bin/release/<triple>/simple` (what `bin/simple` should point at), produced
> by bootstrap. The Rust seed at `src/compiler_rust/target/bootstrap/simple`
> is **bootstrap-only**. If the self-hosted binary is slow or unstable, fix the
> problem in pure-Simple (`src/compiler`, `src/lib`, `src/app`) and re-deploy —
> don't make the seed the default. See `.claude/rules/bootstrap.md`.

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

Bootstrap defaults to `llvm`. `llvm-lib` and `cranelift` remain explicit
supported selections. A missing LLVM installation fails with a direct setup
error; the wrapper never silently changes the requested backend.

### Platform Notes

- **Linux:** LLVM most commonly available. Install `libllvm-18-dev` for `llvm-lib` backend. Preferred linker: `mold`.
- **macOS:** Needs Homebrew LLVM (`brew install llvm`) for the default LLVM backend. Select `--backend=cranelift` explicitly when desired. Linker: system `ld` (ld64).
- **Windows:** Install LLVM for the default backend or select `--backend=cranelift` explicitly. Both MSVC and MinGW toolchains remain supported.

### SimpleOS Multi-Platform Binaries

SimpleOS target metadata is centralized in `src/os/port/simpleos_multiplatform_build.spl`. The catalog lists the Simple entrypoint, linker script, QEMU binary, freestanding C flags, assembly flags, and boot support sources for each OS target.

```bash
# Build all first-class SimpleOS QEMU targets
bin/simple run examples/09_embedded/simple_os/build.spl

# Build 32-bit x86 explicitly
bin/simple run examples/09_embedded/simple_os/build.spl -- --arch=x86_32
bin/simple run examples/09_embedded/simple_os/build.spl -- --arch=i686
```

The 32-bit x86 lane is `i686-simpleos`: C boot support is compiled with `--target=i686-unknown-none-elf -m32`, assembly boot support uses the same i686 freestanding target, QEMU runs with `qemu-system-i386`, and the SimpleOS runner defaults that lane to LLVM because Cranelift does not expose an i686 freestanding target here. Build the selected compiler binary with the Rust `llvm` feature and LLVM 18 available through `LLVM_SYS_180_PREFIX` or system discovery before using this lane.

---

## Bootstrap from Source

The Simple compiler is self-hosted. To build from scratch, a bootstrap process produces the first binary, which then compiles itself.

### Bootstrap Stages

```
Stage 1: Rust Seed Binary
  scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
  # internally rebuilds the Rust seed/runtime only for full bootstrap
  -> src/compiler_rust/target/bootstrap/simple
  -> Backend: Cranelift (hardcoded)

Stage 2: Pure Simple (compiled by Rust seed)
  seed native-build --entry bootstrap_main.spl
  -> build/bootstrap/stage2/<triple>/simple
  -> Backend: selected backend (LLVM default; Cranelift supported)

Stage 3: Self-Hosted (compiled by Stage 2)
  stage2 native-build --entry bootstrap_main.spl
  -> build/bootstrap/stage3/<triple>/simple
  -> Backend: selected backend (LLVM default; Cranelift supported)

Stage 4: Full CLI (compiled by verified stage when available)
  stage3 native-build --entry main.spl
  -> build/bootstrap/full/<triple>/simple
  -> Backend: selected backend (LLVM default; Cranelift supported)
```

After the fresh Stage 4 full CLI passes candidate admission, bootstrap runs
`scripts/check/check-bootstrap-essential-tools-smoke.shs` against that exact
absolute binary before continuing. The bounded gate calibrates the test runner
with green, red, and empty specs; calibrates focused lint with clean and
`STUB003` fixtures; and requires duplicate-check to distinguish a clean file
from one exact clone pair. Any wrong exit or missing marker stops bootstrap.
This is a post-bootstrap sanity gate, not a substitute for release `--whole`
tests or repository-wide lint and duplication policy.

Before Stage 2 is used to build Stage 3, and before Stage 3 is accepted, the
wrapper runs the shared bootstrap compiler sanity: exact bootstrap version,
fail-closed rejection of unsupported `run`, then strict native-build and
execution of the canonical `p2_add.spl` fixture. A failed sanity removes that
stage from consideration on Linux, macOS, Windows/POSIX-shell, and FreeBSD.

The `Rust Bootstrap Multiplatform` workflow runs this canonical stage path with
LLVM and explicit Cranelift on Linux x86_64, macOS AArch64, macOS x86_64, and
Windows x86_64. It uploads Stage 2/Stage 3 pure-Simple artifacts, never the Rust
seed as the platform result.

The Linux Stage 3 artifact then runs
`scripts/check/check-llvm-simd-row-native-arch.shs`: native x86_64 plus QEMU
AArch64 and RISC-V exact-output execution, with target-specific SIMD/RVV
instruction checks. This is the hosted Engine2D native-row architecture gate;
it does not introduce a parallel WebIR, Draw IR, or rendering path.

Current implementation note: Stage 2/Stage 3 are fail-closed while
`bootstrap_main.spl` self-host lowering is still being repaired. When Stage 3
is unavailable, the wrapper reports incomplete pure-Simple evidence and exits
before producing a Stage 4 full CLI; it does not publish a seed fallback as a
self-hosted result.

### Quick Bootstrap

The canonical entrypoint is the host bootstrap wrapper. Normal runs do not
rebuild Rust; they reuse the existing seed/runtime and rebuild only
pure-Simple stages.

```bash
# Default fast path: dynload pure-Simple stages, no cargo
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload

# Relink the full pure-Simple CLI without rebuilding Rust
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload --full-cli

# Conservative monolithic pure-Simple output, no cargo
scripts/bootstrap/bootstrap-from-scratch.sh --mode=one-binary

# Explicit Rust seed/runtime rebuild plus pure-Simple dynload stages
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap

# Rebuild Rust seed/runtime and relink the full CLI
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --full-cli
scripts/bootstrap/bootstrap-from-scratch.sh --release
```

`--release` implies deployment and fails unless the deployed self-hosted
binary passes `simple test test --whole --mode=interpreter`, including long
specs, source-comment doctests, and Markdown embedded-code tests.

On Windows, use the Windows bootstrap wrapper:

```powershell
.\scripts\bootstrap\bootstrap-windows.cmd --deploy
```

Windows stage outputs are executable paths (`stage2/<triple>/simple.exe` and
`stage3/<triple>/simple.exe`). Use `--mingw` or `--msvc` on the Bash wrapper to
override automatic ABI selection. Normal Windows bootstrap uses the same
dynload-only default and explicit full-build policy.

On Windows, stripped native links normalize volatile PE metadata after the
hosted linker returns. The normalizer zeroes the COFF `TimeDateStamp` and PE
optional-header `CheckSum` fields so repeated stripped native-build and
bootstrap outputs can be compared by SHA256.

Use `scripts/bootstrap/bootstrap-from-scratch.sh` for the host bootstrap wrapper.
Normal runs reuse the existing Rust seed/runtime and rebuild only the
pure-Simple stages. Rust seed/runtime rebuilds happen only with
`--full-bootstrap`.

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload
scripts/bootstrap/bootstrap-from-scratch.sh --mode=one-binary
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
```

`dynload` is the default fast-iteration mode. It preserves compiler-owned
per-module cache entries and skips Stage 4. `--full-cli`, `--deploy`,
and `one-binary` request the monolithic native executable. `--full-bootstrap`
alone refreshes Rust inputs but keeps the dynload-only output boundary.

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
| `--backend=X` | Select `llvm` (default), `llvm-lib`, or `cranelift` |
| `--output=DIR` | Write stage outputs to a custom directory |
| `--seed=PATH` | Seed compiler binary. Use `.exe` on Windows. |

### Bootstrap Support Files

| Path | Purpose |
|------|---------|
| `src/compiler_rust/driver/src/cli/commands/misc_commands.rs` | Implements `simple build bootstrap` |
| `src/compiler_rust/native_all/` | Rust static archive used when the Simple compiler links hosted compiler/runtime symbols |
| `src/runtime/runtime_native.c` | C runtime lane used by native bootstrap builds |

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

The platform binary is fully self-sufficient. All compilation, interpretation, and test running happens in-process. The only external tool calls are to system compilers and linkers (`clang`, `gcc`, `mold`/`lld`/`ld`, `llc`). The `scripts/setup/setup.shs` script creates the `bin/simple` symlink pointing to the correct platform binary.

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
