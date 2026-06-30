# Compiler Optimization Levels

**Date:** 2026-04-29

This guide centralizes what optimization groups currently exist and how native executable builds use them.

## Groups

### Syntax optimization

Grouped under [src/compiler/10.frontend/syntax_opt/README.md](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/syntax_opt/README.md).

Current implementation lives in `src/compiler/10.frontend/desugar/` and covers:

- async desugaring
- placeholder lambda rewrite
- collection pattern desugaring
- related syntax-normalization analyses

### MIR optimization

Grouped under `src/compiler/60.mir_opt/`.

Current implemented passes include:

- constant folding
- copy propagation
- dead code elimination
- global value numbering
- common subexpression elimination
- inlining
- loop optimizations
- outlining
- SIMD lowering/vectorization-related passes

Strength reduction includes power-of-two modulo lowering for 64-bit constants,
so native-style queue and ring arithmetic such as `% 128` and
`% 1099511627776` can become bit masks in MIR.

### Native executable optimization

Used by `simple native-build` and `simple compile --native`.

Current implemented native-path controls are:

- release build mode
- 4KB layout optimization
- strip / PIE / shared / map controls
- backend selection with `--backend=cranelift` or `--backend=llvm`

## Levels

### `none`

- Native path: debug build mode
- Layout optimization: disabled

### `basic`

- Native path: release build mode
- Layout optimization: disabled

### `standard`

- Native path: release build mode
- Layout optimization: disabled

### `aggressive`

- Native path: release build mode
- Layout optimization: enabled
- This is the default profile for native executable builds

## Default

`simple native-build` now defaults to the **aggressive** profile so executable builds use the strongest currently implemented native optimization set by default.

## Backend Checks

Use the host-native arithmetic benchmark when checking that both native
backends can compile and run the same Simple workload:

```bash
src/compiler_rust/target/release/simple compile test/05_perf/net_driver_logic_native_bench.spl \
  --native --backend=cranelift --cpu native --opt-level aggressive \
  -o build/perf/net_driver_logic_simple_cranelift
build/perf/net_driver_logic_simple_cranelift

src/compiler_rust/target/release/simple compile test/05_perf/net_driver_logic_native_bench.spl \
  --native --backend=llvm --cpu native --opt-level aggressive \
  -o build/perf/net_driver_logic_simple_llvm
build/perf/net_driver_logic_simple_llvm
```

The parity wrapper `test/05_perf/run_net_driver_logic_parity_bench.shs` covers
the default native backend against the C reference. Run the explicit LLVM
command above when the task needs LLVM evidence too. If the CLI reports that
LLVM is unavailable, rebuild it with:

```bash
cargo build --manifest-path src/compiler_rust/Cargo.toml \
  -p simple-driver --release --features llvm --bin simple
```

## Notes

- Syntax and MIR entries describe currently implemented optimization inventory across the compiler codebase.
- The Rust native executable path does not yet consume every self-hosted MIR optimization entry directly.
- The compile CLI can print the current inventory with `simple compile --list-optimizations`.
- Reusable compiler/interpreter optimization extensions should follow the [Simple Optimization Plugin guide](compiler_optimization_plugin.md). A Simple Optimization Plugin is a general optimization provider for similar programs, not a benchmark-specific rewrite.
