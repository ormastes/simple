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
bin/simple lint <changed .spl files> # Run the pure-Simple source linter
bin/simple build check          # Rust clippy + rustfmt check + Rust tests
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
  SIMPLE_NATIVE_RUNTIME_BUNDLE=all stage2 native-build [forwarded options] bootstrap_main.spl
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
LLVM on Linux x86_64 and macOS AArch64, and with explicit Cranelift on macOS
x86_64 and Windows x86_64. It uploads Stage 2/Stage 3 pure-Simple artifacts,
never the Rust seed as the platform result.

The Linux Stage 3 artifact then runs
`scripts/check/check-llvm-simd-row-native-arch.shs`: native x86_64 plus QEMU
AArch64 and RISC-V exact-output execution, with target-specific SIMD/RVV
instruction checks. This is the hosted Engine2D native-row architecture gate;
it does not introduce a parallel WebIR, Draw IR, or rendering path.

Stage 3 uses the pure-Simple positional `bootstrap_main.spl` path, not the
Rust-owned explicit `--entry` bridge. The wrapper pins
`SIMPLE_NATIVE_RUNTIME_BUNDLE=all` and forwards the selected target, backend,
runtime path, cache directory, thread count, and build mode. Stage 2/Stage 3
remain fail-closed: when Stage 3 is unavailable, the wrapper reports incomplete
pure-Simple evidence and exits before producing a Stage 4 full CLI; it does not
publish a seed fallback as a self-hosted result.

### Provenance-gated incremental promotion

The wrapper seals each accepted Stage 2 in
`build/bootstrap/stage2/<triple>/stage2-provenance.env` plus its `.sha256`
sidecar. Consumers must validate both with
`bootstrap_stage2_verify_manifest`; a binary path and hash alone do not prove
the source, Git, tool, runtime, seed, cache, command, and sanity authorities
recorded by that manifest.

For changes that depend on Option lowering, run
`scripts/check/check-native-option-admission-probes.shs` before promotion. Pin
the exact Stage 2 binary and manifest, source checkpoint, deterministic core-C
capsule, and fresh attempt/cache roots. The wrapper executes isolated A/B/C
native probes for absent, payload-free present, and struct-payload present
values and seals their commands, outputs, formats, and inventory. Manual probe
stdout or reconstructed success counts are not admission evidence.

The active ten-spec SimpleOS shared-font delivery has a narrower Stage2-only
tool contract and does not promote a compiler. First run `sh
scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2` at a clean
pinned checkpoint, then pass its canonical Stage2 binary and provenance
manifest to:

```bash
CHECKPOINT_SHA=<clean-commit-sha> \
STAGE2_PARENT=<canonical-stage2-simple> \
STAGE2_PARENT_SHA=<sha256> \
STAGE2_PROVENANCE_PATH=<canonical-stage2-provenance.env> \
STAGE2_PROVENANCE_SHA=<sha256> \
STAGE2_FONT_TOOL_ATTEMPT_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-<next-number> \
STAGE2_FONT_TOOL_CACHE_ROOT=build/native_probe/shared-font-stage2-scoped-tools-cache/attempt-<next-number> \
bash scripts/check/build-stage2-font-scoped-tools.shs write
```

The wrapper builds and canonically verifies a fresh core-C capsule, then uses
entry closure discovery without broad `--source` roots to build the current
standalone font runner and SPipe docgen as ELF files. It preserves separate
caches, exact command/environment/stream/exit/time and source/tool/runtime
hashes, validates Runtime6 providers including `rt_file_create_excl`, and runs
green, deliberate-red, zero-example, and zero-stub docgen calibration exactly
once. A later independent
audit runs `bash scripts/check/build-stage2-font-scoped-tools.shs check
<attempt-root>`; do not rerun a green writer. This exception is only
`SIMPLEOS_STAGE2_FONT` evidence: Stage 3/4, full bootstrap, general `run`/`test`
qualification, and release remain outside it.

Run the exact ten executable specs once with the same positive-decimal receipt
attempt as the scoped tools; consumed attempt numbers are never reused.
The helper validates and stages the supplied mtools directory, binds all
x86/RV64 host tools, firmware, sysroot inputs, and optional payload state, and
creates no receipt root when preflight fails:

```bash
STAGE2_FONT_SPEC_ATTEMPT=<next-number> \
SIMPLE_FONT_HOST_TOOL_DIR=<absolute-validated-mtools-directory> \
BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live \
REPORT_PATH=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live/report.md \
RV64_DISPLAY_SMOKE_ELF=build/os/simpleos_riscv64_display_smoke.elf \
RV64_WM_FONT_DISK=build/os/fat32-riscv64-desktop.img \
RV64_WM_FONT_REGION_EXPECTED_SHA256=<independently-reviewed-rv64-crop-sha256> \
bash scripts/check/run-stage2-font-scoped-specs.shs write <attempt-root>
STAGE2_FONT_SPEC_ATTEMPT=<same-number> \
bash scripts/check/run-stage2-font-scoped-specs.shs check <attempt-root>
```

After the exact ten scoped specs pass, generate and check their canonical
manuals without rebuilding the tools:

```bash
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-write \
  <attempt-root> <manual-attempt-root>
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-check \
  <attempt-root> <manual-attempt-root>
```

Stage 3 and Stage 4 may then build incrementally from that admitted parent.
Stage 4 evidence is written by
`scripts/check/stage4-provenance-receipt.shs write`, which owns the isolated
build command and transcript and binds before/after source and Git snapshots,
the parent and runtime, deterministic core-C capsule, locked cache, native
output, and output hash. Run the essential-tools smoke against that exact
artifact. Do not replace a missing receipt with a clean rebuild or
`--full-bootstrap`; rebuild Rust only when Rust-owned seed/runtime inputs
changed or the accepted Stage 2 proves that the seed lacks a required
capability.

### Quick Bootstrap

The canonical entrypoint is the host bootstrap wrapper. Normal runs do not
rebuild Rust; they reuse the existing seed/runtime and rebuild only
pure-Simple stages.
`--jobs=N` bounds both private Rust-authority Cargo builds and pure-Simple
native builds, so a recovery run does not silently consume all host CPUs.
When an isolated worktree has lost its ignored Rust seed/runtime tuple, use
`--full-bootstrap --stop-after-stage2 --jobs=1` to rebuild only that authority
and stop after verified Stage 2.

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

### Bounded Stage 4 memory diagnostics

Set `SIMPLE_COMPILER_MEMORY_PROFILE=1` on a bounded Stage 4 or `native-build`
run to emit low-noise `[BOOTSTRAP-PHASE]` elapsed-time and `heap_registry`
live-object receipts. Escalate to `SIMPLE_COMPILER_PHASE_PROFILE=1` only when
the coarse receipts leave the growing sub-phase unclear; both are off by default.

### Cranelift Bootstrap Path (2026-07-18)

The Cranelift backend now completes stages 2–3 successfully as an alternative to LLVM:

```bash
# Bootstrap with Cranelift backend (stages 2–3)
sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift
```

**Notes:**
- Cranelift stages 2–3 complete reliably. A full-CLI (`--full-cli`) rebuild can
  reuse the admitted Stage 3; pair it with `--full-bootstrap` only when changed
  Rust seed/runtime inputs must actually be rebuilt. Stale-backfill rejection
  still applies to a Stage 3 produced by a pre-fix seed.
- **LLVM path status:** Stage 2 link has 62 residual undefined symbols blocking LLVM bootstrap. See [doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md](../../08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md).
- **Stage-4 caveat:** Hours-long spins observed when stage-3 was built by pre-fix seed. Root: InterpCall handicap in Cranelift (symbol lowering delay). See [doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md](../../08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md).

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

The selected ABI is authoritative for the full strict build: Cargo receives
the matching target triple, Rust artifacts stay under that target directory,
and compiler, linker, archive name, manifest, and provenance checks must all
agree. MinGW consumes GNU `.a` archives; MSVC consumes `.lib` archives.

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
