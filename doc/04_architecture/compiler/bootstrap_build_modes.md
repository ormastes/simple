<!-- codex-architecture -->
# Bootstrap Build Modes

## Purpose

Define the bootstrap and pure-Simple native-build mode boundary so compiler,
interpreter, and loader work does not drift back into Rust-seed tooling.

## Modes

| Mode | Default | Build shape | Owner |
|------|---------|-------------|-------|
| `dynload` | yes | Native executable plus SMF cache artifacts where the current driver supports `OutputFormat.Both` | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/80.driver` |
| `one-binary` | no | Monolithic native executable path using `OutputFormat.Native` | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/70.backend` |

`scripts/bootstrap/bootstrap-from-scratch.sh` defaults to `dynload` and reuses
the existing Rust seed/runtime. It must not run cargo unless `--full-bootstrap`
is explicit. The Rust seed is a bootstrap input, not the production toolchain.

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
Until resolver-backed cache keys include source hash, options hash, dependency
interface hashes, and AOP/MDSOC configuration hash, `dynload` cache reuse stays
conservative: bootstrap scripts clear cache on changes under `src/compiler`,
`src/app`, or `src/lib`, and any AOP/MDSOC/weaving environment change is treated
as a broad invalidation.

## Rust Seed Warning

Rust-built `src/compiler_rust/target/bootstrap/simple` prints `WARNING` when run
outside bootstrap. Bootstrap internals set `SIMPLE_BOOTSTRAP=1`; users should
build and use pure-Simple `bin/simple`.

## Cooperative Review

The current lane used read-only sidecars for bootstrap behavior, dynload/loader
surfaces, and dependency tracing/AOP risk. Integration owner is the main Codex
thread; future implementation of resolver-backed incremental rebuilds needs a
normal/high-capability review before claiming production precision.
