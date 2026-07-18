# Bootstrap Build Policy

Status: current policy, updated 2026-07-06.

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

No third mode should be added without a separate requirements decision.

## Backend Selection

LLVM is the default bootstrap backend. `llvm`, `llvm-lib`, and `cranelift` are
supported explicit selections, and every retained stage must use the same
selection. Missing LLVM is a setup error; the wrapper must not silently change
an LLVM request to Cranelift.

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

- `scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload` performs a
  pure-Simple rebuild and does not run cargo.
- `scripts/bootstrap/bootstrap-from-scratch.sh --mode=one-binary` performs a
  pure-Simple monolithic rebuild and clears the native cache.
- `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` may rebuild
  the Rust seed/runtime before pure-Simple stages.
- Direct execution of the Rust seed prints the seed warning outside bootstrap
  mode.
- REQ-BOOT-BACKEND-001: Bootstrap defaults to LLVM, honors explicit LLVM or
  Cranelift selection through every stage, and fails rather than silently
  changing the requested backend.
- REQ-BOOT-BACKEND-002: Native platform CI must exercise LLVM on Linux and
  Apple Silicon, Cranelift on Intel macOS and Windows, run the canonical Stage
  2/Stage 3 sanity, and publish only the pure-Simple stage artifacts.
- REQ-BOOT-ARCH-001: The Linux Stage 3 pure-Simple LLVM artifact must build and
  execute the canonical exact-output SIMD row probe for x86_64, AArch64, and
  RISC-V under native/QEMU execution, including target instruction checks.
- REQ-BOOT-STAGE-001: Every retained Stage 2 and Stage 3 pure-Simple compiler
  must start, compile the canonical tiny redeploy fixture with stub fallback
  disabled, run the produced native binary successfully, and reject unsupported
  commands without misrouting them to `native-build`.
- REQ-MCP-CMD-001: The exact cached native Simple MCP server built by fresh
  pure Stage 2 at `build/bootstrap/mcp-package/simple_mcp_server` must answer
  `initialize`, `notifications/initialized`, and `tools/list`, then serve
  representative `simple_pipe` and `simple_search` calls without runtime stubs,
  source-mode fallback, or Rust-seed fallback.
- REQ-MCP-CMD-002: Every bootstrap route that reaches the full server-producing
  Stage 5 must delete and rebuild the exact cached native MCP/LSP pair, with
  runtime stub fallback disabled, before deployment. Both servers must answer
  `initialize`, `notifications/initialized`, and `tools/list`; the MCP server
  must serve `simple_status` and the LSP server must serve `lsp_symbols`, with
  correlated string response IDs and no source-mode or Rust-seed fallback.
