<!-- codex-architecture -->
# Bootstrap Build Modes

## Purpose

Define the bootstrap and pure-Simple native-build mode boundary so compiler,
interpreter, and loader work does not drift back into Rust-seed tooling.

## Modes

| Mode | Default | Build shape | Owner |
|------|---------|-------------|-------|
| `dynload` | yes | Reusable per-module native/SMF cache plus staged bootstrap artifacts; the wrapper skips the full CLI relink unless explicitly requested | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/80.driver` |
| `one-binary` | no | Monolithic native executable path using `OutputFormat.Native` | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/70.backend` |

`scripts/bootstrap/bootstrap-from-scratch.sh` defaults to `dynload`, reuses the
existing Rust seed/runtime, and stops after the pure-Simple staged build. It
must not run cargo unless `--full-bootstrap` is explicit. Stage 4 full-CLI
relinking requires `--full-cli`, `--deploy`, or `--mode=one-binary`.
`--full-bootstrap` controls only Rust seed/runtime freshness and still stops
after the dynload stages unless combined with a full-CLI option. The Rust seed
is a bootstrap input, not the production toolchain.

A full bootstrap is required only when changed Rust seed/runtime implementation
inputs must actually be rebuilt. Pure-Simple compiler, interpreter, bootstrap,
app, IDE, Office, ordinary tooling, documentation, and test-only changes use
the cheapest adequate incremental or staged pure-Simple build. Reaching a final
completion gate is not by itself a reason to rebuild Rust.

Stage 3 is a pure-Simple positional compile of
`src/app/cli/bootstrap_main.spl`. The wrapper sets
`SIMPLE_NATIVE_RUNTIME_BUNDLE=all`; the bootstrap entry forwards
`--runtime-path`, `--target`, `--cache-dir`, and `--threads` into the in-process
driver environment and restores the caller's values afterward. Explicit
`--entry` remains the Rust-seed-owned Stage 2 bridge and is not the Stage 3
self-host path.

The focused Stage 4 route in
`src/app/cli/bootstrap_focused_native_build.spl` accepts only the canonical
`--low-memory` flag, maps it to `SIMPLE_BOOTSTRAP_LOW_MEMORY` around the
in-process driver call, and restores the caller's prior value afterward.

## Dependency Tracing

`--entry-closure` is a reducer, not an authority. It scans imports from the
entry to avoid loading broad source roots, but the real owner boundary is:

- module resolution: `src/compiler/99.loader/module_resolver/`
- source loading and entry closure env: `src/compiler/80.driver/driver.spl`
- AOP/MDSOC weaving: `src/compiler/85.mdsoc/` plus `driver_pipeline.spl`
- interpreter load/session cache: `src/compiler/10.frontend/core/interpreter/`
- SMF/native artifact output: `src/compiler/80.driver/driver_aot_output.spl`

Cache reuse is safe for unchanged leaf source artifacts. Changes that can alter
weaving, module resolution, interpreter adapters, loader ABI, or compiler ABI
must invalidate broadly. Script-level dependency tracing must never claim more
precision than the compiler resolver can prove.

## Refactor Invalidation Boundary

The broader refactor lane is
`doc/03_plan/agent_tasks/bootstrap_compiler_interpreter_loader_arch_refactor.md`.
The native-build cache owns source-level invalidation and recompiles changed
modules from their source fingerprints. The wrapper invalidates the whole
cache only when platform/backend/mode or AOP/MDSOC/weaving/loader build context
changes, or when `--fresh-cache` is explicit. Use `--fresh-cache` after a
compiler code-generation semantic change or dependency-interface change that
the current per-module metadata cannot prove safe.

## Platform Contract

- macOS uses `shasum -a 256` when GNU `sha256sum` is absent, accepts `gtimeout`
  when installed, and derives Homebrew library paths from `brew --prefix`.
- Windows runs through `bootstrap-windows.cmd` or `bootstrap-windows.sh`, emits
  `.exe`/`.lib` artifacts, and selects `windows-gnu` for MinGW/UCRT or
  `windows-msvc` otherwise.
- FreeBSD runs this same wrapper inside a FreeBSD host. Linux-host verification
  uses `scripts/check/check-freebsd-bootstrap-qemu.shs`; it does not dispatch
  to a separate seed script.

## Rust Seed Warning

Rust-built `src/compiler_rust/target/bootstrap/simple` prints `WARNING` when run
outside bootstrap. Bootstrap internals set `SIMPLE_BOOTSTRAP=1`; users should
build and use pure-Simple `bin/simple`.

## Cooperative Review

The current lane used read-only sidecars for bootstrap behavior, dynload/loader
surfaces, and dependency tracing/AOP risk. Integration owner is the main Codex
thread; future implementation of resolver-backed incremental rebuilds needs a
normal/high-capability review before claiming production precision.
