# Bootstrap Guide (2026-02-28)

This guide is the quick bootstrap reference for the current repository layout.

## Current Layout

- Full compiler sources: `src/compiler/`
- Generated C++20 output: `src/compiler_cpp/`
- Bootstrap scripts: `scripts/bootstrap/`

`src/compiler_core_legacy/` is retired. Bootstrap and docs should use `src/compiler/`.
Runtime files are in `src/runtime/` (previously `src/compiler_seed/`).

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

## Architecture Note (2026-02-28)

The self-hosted binary (`bin/release/simple`) no longer delegates any work to subprocess calls. All compilation backends (C, VHDL, native), file execution, and test running use in-process function calls. The only external tool calls are system compilers/linkers: `clang`/`clang++`, `gcc`, `mold`/`lld`/`ld`, `llc`, `uname`, `which`.

## Related Docs

- `doc/build/bootstrap_pipeline.md`
- `doc/build/github_actions_bootstrap_guide.md`
