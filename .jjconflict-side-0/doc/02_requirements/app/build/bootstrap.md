# Bootstrap Build Policy

Status: current policy, updated 2026-08-16.

## Scope

This note defines the default bootstrap contract for developer rebuilds and CI
lanes that already have a Rust seed binary available.

## Build Modes

Simple bootstrap has two public pure-Simple build modes:

- `dynload` is the default. It reuses the native cache when compiler, app,
  library, loader, interpreter, AOP/MDSOC, and runtime-family inputs have not
  changed.
- `one-binary` is the conservative monolithic mode. It clears the native cache
  and rebuilds a single native executable.

No third code-generation mode should be added without a separate requirements
decision. Bootstrap scheduling strategy is orthogonal to this mode.

## Rust Seed Boundary

Normal bootstrap must not rebuild Rust. It reuses:

- `src/compiler_rust/target/bootstrap/simple`
- `src/compiler_rust/target/bootstrap/libsimple_native_all.a`

Cargo is allowed only for `--full-bootstrap`, or when an explicit seed/runtime
maintenance task is being performed. If the existing seed cannot build the
changed pure-Simple sources, stage 2 must fail loudly and the operator should
rerun with `--full-bootstrap`.

All Rust-built Simple tools are bootstrap seeds. Direct seed use must print a
`WARNING` unless the command is running under `SIMPLE_BOOTSTRAP=1`, explicitly
sets `SIMPLE_RUST_SEED_WARNING=0`, or passes `--seed-ok` / `--rust-seed-ok`.
Day-to-day build, test, lint, MCP, LSP, and run workflows must use the
pure-Simple `bin/simple` / `bin/release/<triple>/simple` path.

## Dependency Tracing

The native cache key must remain conservative around inputs that can affect
generated code or loaded module identity:

- `src/compiler/**/*.spl`
- `src/app/**/*.spl`
- `src/lib/**/*.spl`
- selected `SIMPLE_*` environment knobs for AOP, MDSOC/weaving, loader,
  interpreter, execution, library path, and native-build behavior
- backend and build mode

This intentionally over-invalidates around AOP. Advice weaving, runtime
interception, and MDSOC policy can change behavior without an obvious direct
source import edge, so cache reuse is allowed only when those inputs match.

## Acceptance

- REQ-BOOT-STRATEGY-001: omitted strategy selects `normal`; invalid strategies
  fail before a compiler starts; `--mode` remains orthogonal.
- REQ-BOOT-STRATEGY-002: normal verification uses isolated incremental caches,
  immutable admitted compilers, and never permits concurrent writers to one
  cache/output.
- REQ-BOOT-STRATEGY-003: full strategy records exit/signal/timeout for every
  runnable task, records blocked descendants, continues independent tasks, and
  reaches a complete terminal summary before returning aggregate failure.
- REQ-BOOT-STRATEGY-004: a normal receipt may satisfy a full task only when its
  compiler, runtime, source, command, and artifact hashes match exactly.
- `scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload` performs a
  pure-Simple rebuild and does not run cargo.
- `scripts/bootstrap/bootstrap-from-scratch.sh --mode=one-binary` performs a
  pure-Simple monolithic rebuild and clears the native cache.
- `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` may rebuild
  the Rust seed/runtime before pure-Simple stages.
- Direct execution of the Rust seed prints the seed warning outside bootstrap
  mode.
