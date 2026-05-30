# LLVM Optimization Workflow

**Date:** 2026-05-12
**Status:** Active

This guide is the practical workflow for keeping Simple's LLVM path and native optimization work grounded in evidence. The detailed implementation log lives in [`../../plans/port_rust_c_to_pure_simple.md`](../../plans/port_rust_c_to_pure_simple.md).

## Core Rule

Simple does not implement LLVM CPU backends for existing CPU targets. Simple emits valid LLVM IR plus exact target configuration; LLVM supplies the optimizer, target backend, instruction selection, register allocation, object emission, and related tooling.

Simple-owned HIR/MIR/pattern/interpreter optimizations should use the [Simple Optimization Plugin](../compiler_optimization_plugin.md) contract. That contract is separate from LLVM pass plugins: it improves Simple's own IR and semantic facts before LLVM receives the module.

Simple is responsible for:

- Frontend semantics: parse, type check, resolve names, lower generics, traits, patterns, and language rules.
- HIR/MIR lowering: produce optimizer-friendly compiler IR before LLVM.
- LLVM IR generation: functions, blocks, PHIs, loads/stores, GEPs, calls, attrs, metadata, and debug/profile data.
- Target configuration: triple, datalayout, CPU, features, ABI, relocation model, code model, runtime symbols, and linker inputs.
- Runtime and linking: allocator, panic/unwind policy, startup, FFI, memory helpers, libc mode, and final linker configuration.

## Optimization Level Mapping

Use LLVM's default new-pass-manager pipelines as the production default. Keep hand-written pass lists for diagnostics or narrowly justified custom paths.

| Simple level | LLVM pipeline |
|--------------|---------------|
| `-O0` | verify only, preserve debug quality |
| `-O1` | `default<O1>` |
| `-O2` | `default<O2>` |
| `-O3` / `aggressive` | `default<O3>` |
| `-Os` / `size` | `default<Os>` |
| `-Oz` | `default<Oz>` |

Relevant files:

- `src/compiler/70.backend/backend/llvm_passes.spl`
- `src/compiler/70.backend/backend/llvm_target.spl`
- `src/compiler/70.backend/backend/llvm_lib_backend.spl`
- `src/compiler/70.backend/backend/llvm_backend_tools.spl`
- `src/compiler_rust/compiler/src/codegen/llvm/`

## IR Quality Checklist

Before tuning pass lists, make the emitted IR correct and rich enough for LLVM to optimize.

- Module has target triple and target datalayout.
- Function linkage, visibility, calling convention, parameter attributes, and return attributes are correct.
- Blocks have terminators, PHIs are valid, and loop structure is canonical where practical.
- Type layout follows the target datalayout for pointers, aggregates, enums, arrays, vectors, padding, and alignment.
- Loads/stores/GEPs use correct types and alignment.
- Memory operations use `memcpy`, `memmove`, or `memset` intrinsics for bulk operations where appropriate.
- Attributes and metadata are emitted only when proven. Incorrect `nonnull`, `noundef`, `noalias`, `dereferenceable`, `nsw`, `nuw`, `exact`, or fast-math flags are wrong-code bugs.

## Verification Commands

Run the smallest command that proves the claim, then keep the evidence in the plan or report.

```bash
cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler --features llvm

cargo test --manifest-path src/compiler_rust/Cargo.toml \
  -p simple-compiler --features llvm \
  create_module_emits_target_triple_and_datalayout -- --nocapture

bin/simple check test/perf/port_algorithms/port_algorithms_simple.spl

SIMPLE_LLVM_PROBE=1 SIMPLE_DISASM_PROBE=1 \
  test/perf/port_algorithms/run_port_algorithm_benchmarks.shs

test/perf/run_comparison.shs
```

When a `.ll` or bitcode emission surface is available, also verify with LLVM tools:

```bash
opt -verify input.ll -o /dev/null
opt -verify-each -passes='default<O2>' input.ll -o output.bc
opt -time-passes -passes='default<O2>' input.ll -o output.bc
```

## Benchmark Acceptance Gate

For algorithm-port work, speed numbers count only after checksum parity passes.

Acceptance for the current XXHash64 and ChaCha20 gate:

- C, Rust, Simple default, and Simple LLVM outputs have matching checksums.
- Self-hosted Simple is no slower than the Rust bootstrap in `test/perf/run_comparison.shs`.
- Pure Simple native reaches at least 70% of portable Rust throughput and 50% of portable C throughput.
- Simple LLVM reaches the same target when the LLVM probe is enabled.

The 2026-05-12 accepted local sample:

| Algorithm | C MB/s | Rust MB/s | Simple default MB/s | Simple LLVM MB/s |
|-----------|--------|-----------|---------------------|------------------|
| XXHash64 | 8415 | 8415 | 8256 | 8282 |
| ChaCha20 | 182 | 195 | 203 | 206 |

## Hot-Path Optimization Pattern

Use this order when a Simple algorithm is slower than the C/Rust reference:

1. Prove checksum parity first.
2. Capture C, Rust, Simple default, and Simple LLVM benchmark rows.
3. Enable `SIMPLE_DISASM_PROBE=1` and inspect call boundaries and runtime helpers.
4. Fix semantic IR facts before adding pass complexity: target layout, typed byte access, length/index facts, inlining visibility, and attributes.
5. Add targeted regression tests for the lowering change.
6. Rebuild the active release artifact when benchmark evidence depends on compiler changes.
7. Update the plan with the command, numbers, artifact hash, and remaining hardening only after the gate passes.

## Current Hardening Backlog

These are not blockers for the 2026-05-12 Phase 6 acceptance gate, but they are the next useful work:

- Add an LLVM IR dump mode so external `opt -verify` and `opt -verify-each` can be run on Simple-generated modules.
- Generalize typed byte/index proof beyond the benchmark hot paths.
- Lower more fixed-size byte-buffer patterns to stack/native storage.
- Keep explicit pass lists available as diagnostics, while the production LLVM path uses `default<O*>`.
