# Bootstrap Guide (2026-03-05)

This guide is the quick bootstrap reference for the current repository layout.

## Current Layout

- Full compiler sources: `src/compiler/`
- Generated C++20 output: `src/compiler_cpp/`
- Bootstrap scripts: `scripts/bootstrap/`

`src/compiler_core_legacy/` is retired. Bootstrap and docs should use `src/compiler/`.
Runtime files are in `src/runtime/` (previously `src/compiler_seed/`).

## Bootstrap Stages & Default Backends

The Simple compiler goes through multiple stages to reach a fully self-hosted binary.
Each stage uses a different default backend for compilation. The backend selection logic
(`get_effective_backend_name()`) is platform-agnostic — the same code runs on Linux, macOS,
and Windows. What differs per platform is LLVM library availability and linker toolchain.

```
Stage 1: Rust Bootstrap Binary
  Build:   cargo build --profile bootstrap -p simple-driver
  Binary:  src/compiler_rust/target/bootstrap/simple
  Backend: Cranelift (Rust, hardcoded)
  Role:    Interprets .spl files and compiles via native-build

    │
    │  native-build (always Cranelift)
    ▼

Stage 2: Pure Simple (compiled by Cranelift)
  Build:   simple native-build
  Binary:  bin/release/simple_native  (or bin/release/simple)
  Backend: Cranelift (no --backend flag for native-build)
  Role:    Natively compiled Simple compiler — runs all Pure Simple code

    │
    │  build --release  (auto backend selection)
    ▼

Stage 3: Full Pure Simple (self-hosted)
  Build:   bin/release/simple build --release
  Binary:  bin/release/simple
  Backend: auto → LLVM-lib (if libLLVM available) → LLVM llc (if llc available) → Cranelift
  Role:    Self-hosted compiler that compiled itself
```

### Default Backend Selection Per Stage

| Stage | Command | Backend | Selection Logic |
|-------|---------|---------|-----------------|
| **Rust bootstrap** | `native-build` | **Cranelift** | Hardcoded in Rust `NativeProjectBuilder` (`codegen/cranelift.rs`) |
| **Pure Simple** (debug) | `build` | **Cranelift** | `get_effective_backend_name("auto", false)` → `"cranelift"` |
| **Pure Simple** (release) | `build --release` | **LLVM-lib** | `get_effective_backend_name("auto", true)` → `"llvm-lib"` if `libLLVM` available → `"llvm"` if `llc` available → `"cranelift"` fallback |
| **Full Pure Simple** | `compile --backend=X` | **explicit** | User-specified backend, no auto-selection |

### Backend Resolution Code

From `src/compiler/70.backend/backend/backend_helpers.spl`:

```simple
fn get_effective_backend_name(backend_name: text, is_release: bool) -> text:
    if backend_name == "auto":
        if is_release:
            if llvm_available():   # libLLVM dynamic library
                "llvm-lib"
            elif llc_available():  # llc command-line tool
                "llvm"
            else:
                "cranelift"
        else:
            "cranelift"            # debug always uses Cranelift
```

### Why Each Stage Uses Its Backend

1. **Rust bootstrap → Cranelift**: The `NativeProjectBuilder` in Rust directly uses the `cranelift` crate. No backend selection logic — Cranelift is the only compiled-in codegen. Fast compilation, no external dependencies.

2. **Pure Simple debug → Cranelift**: Debug builds prioritize compile speed. Cranelift compiles ~2.5x faster than LLVM. Good enough code quality for development iteration.

3. **Pure Simple release → LLVM-lib**: Release builds prioritize runtime performance. LLVM generates 4-5x faster code than Cranelift for compute-bound workloads (measured: fib(35) runs in ~40ms vs ~190ms). Uses `libLLVM` via dynamic FFI (`spl_dlopen`), so requires `libllvm-18-dev` (or equivalent) to be installed.

4. **Fallback chain**: If LLVM is not installed, release builds gracefully fall back to `llc` (LLVM text IR → object file) or Cranelift.

### Platform-Specific Notes

#### Linux

- LLVM library: `libLLVM-18.so` (install `libllvm-18-dev` or equivalent)
- Linker: `mold` (preferred), `lld`, or system `ld`
- LLVM is most commonly available on Linux — release builds typically get `llvm-lib`

#### macOS

- LLVM library: `libLLVM-18.dylib` (install via `brew install llvm`)
- Default macOS (Xcode CLT only, no Homebrew LLVM) → Cranelift for all stages
- Linker: system `ld` (ld64) — `mold` is not supported on macOS
- Homebrew LLVM path must be discoverable by `spl_dlopen` for `llvm-lib` backend

#### Windows

- Dual-toolchain support: MSVC (`clang-cl` / `link.exe`) and MinGW/GNU (`clang` / `ld`)
- CMake bootstrap auto-detects `clang-cl` on Windows for MSVC ABI compatibility
- LLVM dynamic library rarely available on Windows → typically falls back to Cranelift
- Windows system libraries always linked: `kernel32`, `ws2_32`, `bcrypt`, `userenv`
- Linker flags differ by flavor: MSVC uses `/WHOLEARCHIVE`, `/FORCE:UNRESOLVED`; GNU uses `--whole-archive`, `--unresolved-symbols`

### Cross-Platform Default Backend Summary

| Stage | Linux | macOS (with brew LLVM) | macOS (no brew LLVM) | Windows |
|-------|-------|------------------------|----------------------|---------|
| **Stage 1** (Rust bootstrap) | Cranelift | Cranelift | Cranelift | Cranelift |
| **Stage 2** (debug build) | Cranelift | Cranelift | Cranelift | Cranelift |
| **Stage 3** (release build) | LLVM-lib | LLVM-lib | Cranelift | Cranelift |

The fallback chain for Stage 3 release builds is: `llvm-lib` → `llvm` (llc) → `cranelift`.
The effective backend depends solely on whether `libLLVM` or `llc` can be found at runtime.

## Bootstrap Fallback Chain

The bootstrap script uses a two-phase strategy:

```
Phase 0: Download latest release binary from GitHub
    ↓ (success → use it)
    ↓ (fail → continue)
Phase 1–3: Build from C source via CMake + Ninja
```

### Quick Start

```bash
# Automatic: try release download first, fall back to C bootstrap
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Download release binary only (no C build)
scripts/bootstrap/download-release.sh --output=bin/release/simple

# Force C bootstrap (skip release download)
scripts/bootstrap/bootstrap-from-scratch.sh --skip-download --deploy

# Pin to a specific release version
scripts/bootstrap/bootstrap-from-scratch.sh --download-version=0.7.0 --deploy
```

### Flags

| Flag | Description |
|------|-------------|
| `--deploy` / `--update-release` | Copy result to `bin/release/simple` |
| `--skip-download` | Skip release download, force C bootstrap build |
| `--download-version=X.Y.Z` | Pin release download to a specific version |
| `--keep-artifacts` | Keep `build/` directory after completion |
| `--step=full2` | Run self-host verification after build |
| `--jobs=N` | Parallel build jobs (default: 7) |

## Release Binary Download

The `download-release.sh` script fetches a pre-built binary from GitHub releases:

```bash
# Download latest release
scripts/bootstrap/download-release.sh

# Download specific version
scripts/bootstrap/download-release.sh --version=0.7.0

# Custom output path
scripts/bootstrap/download-release.sh --output=/tmp/simple
```

It auto-detects your platform (linux-x86_64, darwin-arm64, etc.), downloads the matching `.spk` package, extracts the binary, and verifies it with `--version`. Uses `gh` CLI when available, falls back to `curl`.

## C Backend Bootstrap (fallback pipeline)

The C backend emits C++20 from the full compiler and builds it with CMake + Ninja + Clang:

```bash
# 1. Generate C++20 from compiler source
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl

# 2. Build with CMake + Ninja
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build

# 3. Install bootstrap binary
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple

# 4. Self-host verification
bin/bootstrap/cpp/simple build
```

Or use the bootstrap script with `--skip-download`:

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --skip-download --deploy
```

## Script Map

| Script | Purpose |
|--------|---------|
| `scripts/bootstrap/download-release.sh` | Download release binary from GitHub |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | Full bootstrap (release download + C fallback) |
| `scripts/bootstrap/bootstrap-c.sh` | C backend bootstrap (CMake + Ninja) |

## Expected Output

- Final binary: `bin/release/simple` — **fully self-sufficient** (all compilation, interpretation, and test running happens in-process via direct function calls like `aot_c_file()`, `compile_native()`, `interpret_file()`)
- C backend bootstrap binary: `bin/bootstrap/cpp/simple`
- Intermediate artifacts: `build/bootstrap/`

## Architecture Note (2026-03-05)

The self-hosted binary (`bin/release/simple`) no longer delegates any work to subprocess calls. All compilation backends (C, VHDL, native), file execution, and test running use in-process function calls. The only external tool calls are system compilers/linkers: `clang`/`clang++`, `gcc`, `mold`/`lld`/`ld`, `llc`, `uname`, `which`.

## Related Docs

- `doc/build/bootstrap_pipeline.md`
- `doc/build/github_actions_bootstrap_guide.md`
- `doc/design/backend_architecture.md` — Backend architecture, compilation paths, and why only Cranelift can bootstrap
- `doc/design/backend_default_decision.md` — Decision doc for making LLVM the default release backend
