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

If Stage 2 was already admitted but Stage 3 was externally killed, resume only
through `scripts/bootstrap/bootstrap-from-scratch.sh
--resume-stage3-from-admitted=OUTPUT --jobs=1`.
The recovery uses a separate evidence lane, one self-host worker, the frozen
admitted compiler/runtime, and fails if source, git, tool, or runtime snapshots
change. It never rebuilds Stage 2.
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
LLVM on Linux x86_64 and macOS AArch64, and with explicit Cranelift on macOS
x86_64 and Windows x86_64. It uploads Stage 2/Stage 3 pure-Simple artifacts,
never the Rust seed as the platform result.

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

As of 2026-08-14, do not infer Stage 3 admission from the historical LIM-010
duplicate-LLVM-constructor repair. The tracked `bootstrap/stage{1,2,3}` files
are byte-identical and the Stage 3 file has no canonical provenance receipt;
it also retains independently tracked tagged-value/list and direct-call-zero
crashes. See
`../../08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`
and
`../../08_tracking/bug/stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md`.
A current PASS requires the exact candidate, manifest, sanity evidence, source
snapshot, command transcript, build log, and stable hashes emitted by the
canonical bootstrap transaction. A live process is pending evidence, not PASS.

### Standalone target builds (Office and similar products)

A target product is not a compiler rebuild. Reuse the last **admitted Phase 3
compiler** when it is suitable, and keep product outputs and incremental cache
outside `build/bootstrap/`. The target wrapper verifies the compiler's Phase 3
provenance before it invokes `native-build`; a stale, symlinked, seed, or
unreceipted binary fails closed. It never starts Stage 1, Stage 2, or Stage 3.

For Office, set the explicit compiler path and run the target-only wrapper:

```bash
SIMPLE_TARGET_PHASE3="$PWD/build/bootstrap/stage3/<triple>/simple" \
  sh scripts/check/build-office-standalone-target.shs
```

The default product output is
`build/standalone/office/<triple>/simple-office`, with a stable cache under
`build/standalone/cache/office/<triple>`. This produces a native product
artifact, not a Stage 4 deploy, SPipe runner, or release admission. When no
admitted Phase 3 receipt exists, record the compiler-admission blocker; do not
fall back to the Rust seed or launch a fresh bootstrap automatically.

| Surface | Classification | Current target-only status |
|---|---|---|
| `src/app/office` | Standalone product | Wired through `build-office-standalone-target.shs` |
| `src/app/devhub`, `src/app/play` | Separate applications | Need their own explicit target wrappers; do not use bootstrap by default |
| `src/app/cli`, `src/compiler`, `src/app/mcp`, `src/app/simple_lsp_mcp` | Compiler/toolchain-owned | Remain compiler/deploy lanes, not standalone-product wrappers |

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

### Cranelift Bootstrap Path (2026-07-18)

The Cranelift backend now completes stages 2–3 successfully as an alternative to LLVM:

```bash
# Bootstrap with Cranelift backend (stages 2–3)
sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift
```

**Notes:**
- Cranelift stages 2–3 complete reliably; full-CLI (`--full-cli`) requires `--full-bootstrap` to avoid stale-backfill rejection (the driver rejects a stage-3 binary built by a pre-fix seed).
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

For long runs, enable the permanent low-overhead progress log:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --progress --progress-interval=30
```

The default `build/bootstrap/bootstrap-progress.log` is append-only and uses
`key=value` records. Milestone records identify Stage 2 through Stage 6 when
reached. Periodic samples report the bootstrap PID, `alive`/`exited`/`stale`
state, elapsed time, CPU percentage, RSS KiB, and current main-log byte size.
Set `--progress=/path/to/log` or `SIMPLE_BOOTSTRAP_PROGRESS_LOG`; adjust cadence
with `SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL`. The watcher reads only process
metadata, a two-line state file, and file metadata; it performs no repeated
source/cache tree scans. The wrapper trap stops it and records the exit status.
Normal runs reuse the existing Rust seed/runtime and rebuild only the
pure-Simple stages. Rust seed/runtime rebuilds happen only with
`--full-bootstrap`.

### Bootstrap debug and test modes

The default diagnostics mode is `off` and adds no flags, files, scans, or
subprocesses. Enable bounded test evidence with:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --diagnostics=test
```

This implies `--progress` and enables coarse phase timing without parser-level
trace. For an investigation that also needs detailed phase trace, successful
LLVM IR, and memory snapshots, use:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --diagnostics=debug
# Bare --diagnostics is the same as --diagnostics=debug.
```

The equivalent environment selector is
`SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE=debug|test`. Explicit existing flag values
still win. Debug artifacts can consume substantial disk space; remove them
after capturing the failing evidence.

AOP instrumentation is deliberately not implied. Enable it only for a scoped
compiler-weaving investigation, preferably with a filter:

```sh
SIMPLE_AOP_DEBUG='module_or_function_pattern' \
SIMPLE_AOP_LOG_CALLS=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh --diagnostics=debug
```

`SIMPLE_AOP_LOG_ASSIGNMENTS=1` is still more verbose and should be added only
when assignment join points are required. See
`doc/07_guide/app/testing/logging.md` for AOP log levels and filters.

For a focused check, `simple check --phase-profile <path>` emits coarse
source-read, parse, lint, teardown, file-total, and command-total records.
Phase records are suppressed with `--json` so machine-readable stdout remains
pure. Diagnostic sweeps bind both `SIMPLE_BINARY` and `SIMPLE_BIN` to an
absolute admitted child executable. In an isolated worktree, select it with
`--diagnostic-child-compiler=/absolute/path/to/simple` or
`SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER`.

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
| `--diagnostics=MODE` | Select default-off `test` or `debug` observability |
| `--diagnostic-child-compiler=PATH` | Bind diagnostic checks to an admitted pure-Simple worker |
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
# Bootstrap diagnostic sweep

When a staged bootstrap stops at the first broken module, run the check-only
diagnostic mode to discover independent errors in one pass:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --diagnostic-sweep \
  --diagnostic-root=src/compiler --jobs=4
```

The mode invokes `check` in an isolated process for every selected `.spl` file,
continues after failures, groups captured output by source path, and exits `1`
when any check fails. Each path has a stable private directory below
`<output>/diagnostic-cache`, so incremental state survives later sweeps while
parallel workers never write the same cache. This is intentionally diagnostic
only: combining it with `--deploy`, `--release`, or `--full-cli` is rejected,
and the mode has no artifact admission or deployment path.

The shell mode is appropriate for short probes. For an inventory-to-end run,
use the compiled checker so the manifest and terminal rows survive interruption:

```sh
python3 scripts/check/compiled-check-tree.py \
  --checker=/absolute/path/to/simple-check \
  --root=src/compiler --root=src/app --root=src/lib \
  --output-dir=build/mini_builds/full-tree-check \
  --workers=4 --batch-size=64 --timeout=120
```

The runner freezes `manifest.tsv` and `run.json`, writes a terminal result for
each batch, and isolates members of failed or timed-out batches per file. Resume
only the same checker/manifest with `--resume`; do not treat the shell sweep's
temporary rows as durable inventory evidence.

Choose the recovery mode before starting:

- **Fail-fast** is the default for CI, release, and a hard blocker that prevents
  later compilation.
- **Inventory-to-end** is for many-error incidents. Freeze the source revision,
  compiler/runtime identities, target, roots, and deterministic manifest; let
  every selected task finish or time out before changing source.

For inventory-to-end runs, retain per-task state and expose manifest total,
completed, failed, remaining, throughput, and ETA. Group results by normalized
first real diagnostic after the sweep. Collapse duplicate/cascade failures,
record and claim each unique root-cause category in the bug database, and assign
categories—not individual files—to parallel agents. Agents use isolated caches
and non-overlapping owner files. Each category fix needs an exact reproducer and
adjacent/similar-situation tests.

Rerun only failed shards with their existing caches, then run the main bootstrap
once. If it produces a CLI, sanity-check it and exercise all supported feature
commands available on the host; feed new runtime failures back into the same
categories. A seed/check sweep never proves Stage 4: record the exact executable,
mode, host, target, and manifest for every claim. Stop after three verify/fix
cycles; remaining categories are reported, not hidden by an endless retry loop.

When per-file startup cost makes the manifest impractical, use bounded compiled
checker batches first. Preserve resume state and measured ETA if an even coarser
module/root manifest is required. Do not fall back to repeatedly fixing only the
first reported error.

## Post-bootstrap acceptance

After full Stage 4, the exact candidate runs
`test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl` with its
absolute candidate and adjacent provenance paths. The checker is read-only and
confirms retained smoke before/after; never repeat an unchanged green smoke run.
