# Backend Architecture — Current State (2026-03)

**Date**: 2026-03-05
**Status**: Living document — reflects actual working state

---

## Executive Summary

The Simple compiler has **9 backends** spanning production compilation, GPU compute, hardware synthesis, and formal verification. The key architectural split:

- **Cranelift (Rust FFI)**: Only working bootstrap path. Production-grade via `native-build`.
- **C backend (Pure Simple)**: Works end-to-end via `mir_to_c.spl` → C++20 → clang.
- **LLVM llc (Pure Simple)**: Text-based IR generation works for small programs, **cannot bootstrap** (interpreted pipeline OOM at ~27GB).
- **LLVM lib (Rust inkwell)**: ~60% MIR instruction coverage. Target to become the default backend for release builds.

**Bottom line**: Only `native-build` (Cranelift via Rust) can compile the full compiler today.

---

## Architecture Diagram

```
┌───────────────────────────────────────────────────────┐
│                Simple Source (.spl)                     │
└──────────────────────────┬────────────────────────────┘
                           │
              ┌────────────┴────────────┐
              │  Rust Bootstrap Binary   │  (bin/release/simple)
              │  Parse → HIR → MIR      │
              └────────────┬────────────┘
                           │
      ┌────────────────────┼────────────────────┐
      │                    │                    │
      ▼                    ▼                    ▼
┌───────────┐      ┌─────────────┐      ┌──────────────┐
│ Cranelift  │      │ Interpreter │      │ Pure Simple   │
│ (Rust FFI) │      │ (Rust)      │      │ Compiler      │
│            │      │             │      │ (interpreted) │
└─────┬──────┘      └──────┬──────┘      └──────┬────────┘
      │                    │                    │
      │                    │           ┌────────┼────────┐
      ▼                    ▼           ▼        ▼        ▼
   .o files            execute      C backend LLVM llc  Others
      │                in-proc      (clang)   (llc-18)  (stub)
      │                              │         │
      ▼                              ▼         ▼
   native-build                   native     .o files
   (mold/lld/ld)                  binary     (linker)
```

**Two worlds**:
1. **Rust-level backends** (Cranelift, LLVM lib) — run natively in the bootstrap binary, can handle full compiler
2. **Pure Simple backends** (C, LLVM llc, VHDL, etc.) — run interpreted by the bootstrap binary, OOM on large programs

---

## Backend Inventory

| Backend | Implementation | Language | Status | Bootstrap? | Key Files |
|---------|---------------|----------|--------|------------|-----------|
| **Cranelift** | `NativeProjectBuilder` | Rust | Production | **Yes** | `compiler_rust/.../cranelift.rs`, `cranelift_emitter.rs`, `cranelift_ffi.rs` |
| **C (C++20)** | `mir_to_c.spl` | Pure Simple | Working | Via clang | `backend/c_backend.spl`, `c_backend_translate.spl`, `c_ir_builder.spl` |
| **LLVM llc** | `mir_to_llvm.spl` | Pure Simple | Working* | **No** (OOM) | `backend/llvm_backend.spl`, `llvm_ir_builder.spl`, `mir_to_llvm.spl` |
| **LLVM lib** | inkwell bindings | Rust | ~60% | Future default | `compiler_rust/.../codegen/llvm/` (11+ files) |
| **Native** | Pure Simple codegen | Pure Simple | Experimental | No | `backend/native/` (30 files: isel, encode, regalloc per arch) |
| **VHDL** | `vhdl_backend.spl` | Pure Simple | Complete | N/A | `backend/vhdl_backend.spl`, `vhdl_builder.spl` |
| **WebAssembly** | `wasm_backend.spl` | Pure Simple | ~20% | N/A | `backend/wasm_backend.spl`, `wasm_codegen_adapter.spl` |
| **CUDA** | `cuda_backend.spl` | Pure Simple | ~20% | N/A | `backend/cuda_backend.spl`, `ptx_builder.spl`, `cuda_launcher.spl` |
| **Vulkan** | `vulkan_backend.spl` | Pure Simple | ~15% | N/A | `backend/vulkan_backend.spl`, `spirv_builder.spl` |
| **Lean** | `lean_backend.spl` | Pure Simple | ~15% | N/A | `backend/lean_backend.spl`, `lean_mir_translate.spl` |

\* Works for small programs, cannot compile full compiler (interpreted pipeline uses >27GB RAM)

### File Locations

- **Pure Simple backends**: `src/compiler/70.backend/backend/`
- **Pure Simple linker**: `src/compiler/70.backend/linker/`
- **Rust Cranelift**: `src/compiler_rust/compiler/src/codegen/cranelift*.rs`
- **Rust LLVM lib**: `src/compiler_rust/compiler/src/codegen/llvm/`
- **Rust native project**: `src/compiler_rust/compiler/src/pipeline/native_project.rs`
- **Rust linker**: `src/compiler_rust/compiler/src/linker/`
- **Backend helpers**: `src/compiler/70.backend/backend/backend_helpers.spl`

---

## Compilation Paths

| CLI Command | Backend | Impl | Works? | Notes |
|-------------|---------|------|--------|-------|
| `native-build` | Cranelift (Rust) | `NativeProjectBuilder` | **Yes** | Only working full-compiler path |
| `compile --native` | C → clang | `aot_c_file()` | Yes (small) | Legacy path, single-file |
| `compile --backend=llvm` | LLVM llc (Simple) | Interpreted driver | No (OOM) | Runs entire pipeline interpreted |
| `compile --backend=cranelift` | Cranelift (Simple) | Interpreted driver | No (OOM) | Same OOM issue |
| `compile --backend=c` | C (Simple) | Interpreted driver | No (OOM) | Same OOM issue |
| `build --release` | LLVM llc → Cranelift fallback | `get_effective_backend_name()` | Partial | Works for small programs via LLVM llc |

### Why `compile --backend=X` Cannot Bootstrap

The Rust bootstrap binary interprets `main.spl` → `cli_compile()` → `cli_compile_pure_simple()`. This creates a Pure Simple `CompilerDriver` which runs the **entire compilation pipeline interpreted**. For the full compiler (~2600 files, ~623K lines), interpretation uses >27GB RAM and gets OOM-killed.

The `native-build` command bypasses this entirely — it uses the Rust-native `NativeProjectBuilder` which runs Cranelift codegen directly in compiled Rust code.

---

## Backend Selection Logic

### Current Implementation (`get_effective_backend_name()`)

Located in `src/compiler/70.backend/backend/backend_helpers.spl`:

- `auto` + release → LLVM (if `llc` available) else Cranelift
- `auto` + debug → Cranelift
- Explicit `--backend=X` → X

### What Actually Works for Bootstrap

- Only `native-build` → Cranelift (Rust) works for the full compiler
- No `--backend` flag exists for `native-build` (always Cranelift)

---

## Pure Simple Native Backend

The `src/compiler/70.backend/backend/native/` directory contains an ambitious **pure Simple native code generator** with:

- **Instruction selection**: `isel_x86_64.spl`, `isel_aarch64.spl`, `isel_riscv64.spl`, `isel_riscv32.spl`
- **Machine code encoding**: `encode_x86_64.spl`, `encode_aarch64.spl`, `encode_riscv64.spl`, `encode_riscv32.spl`
- **Object file writers**: `elf_writer.spl`, `macho_writer.spl`
- **Register allocation**: `regalloc.spl`
- **SIMD**: `arm_neon.spl`, `x86_64_simd.spl`

This backend generates machine code directly without external tools, but is experimental and not yet capable of compiling real programs.

---

## Linker Infrastructure

### Pure Simple (`src/compiler/70.backend/linker/`)

37 files covering:
- **SMF format** (Simple Module Format): `smf_writer.spl`, `lib_smf.spl`
- **Object linking**: `link.spl`, `linker_wrapper.spl`, `object_resolver.spl`
- **Dynamic linking**: `dynamic_link.spl`
- **Platform support**: ELF and Mach-O writers

### Rust (`src/compiler_rust/compiler/src/linker/`)

- `native.rs`, `native_binary.rs` — native linking
- `mold_ffi.rs` — mold linker integration
- `smf_writer.rs` — SMF format (Rust impl)

### External Linkers

The compiler shells out to system linkers: `mold` (preferred) → `lld` → `ld` (fallback).

---

## Current Limitations

1. **Pure Simple backends cannot bootstrap**: All `compile --backend=X` paths run interpreted, OOM on full compiler (~27GB)
2. **LLVM lib (inkwell) ~60% instruction coverage**: Many MIR instructions stubbed, not yet usable for compilation
3. **Cranelift Pure Simple adapter is a stub**: `cranelift_codegen_adapter.spl` delegates to Rust FFI, no standalone Pure Simple Cranelift
4. **No backend choice for `native-build`**: Always uses Cranelift, no `--backend` flag
5. **Native codegen experimental**: Pure Simple native backend (x86_64/aarch64/riscv) not yet production-ready

---

## Roadmap

### Phase 1: Current (v0.8.0) — Cranelift-only bootstrap

- `native-build` → Cranelift (Rust) → native binary
- LLVM llc works for small programs only
- C backend works end-to-end for small programs

### Phase 2: LLVM lib completion → default for release

- Complete LLVM lib (inkwell) P0 MIR instructions in Rust
- Wire into `NativeProjectBuilder` as alternative to Cranelift
- Add `native-build --backend=llvm` flag
- Validate with full compiler compilation

### Phase 3: Pure Simple migration

- Once self-hosted compiler is natively compiled, Pure Simple backends run natively (not interpreted)
- Pure Simple backends become viable for bootstrap
- Replace Rust FFI dependencies with Pure Simple implementations

### Phase 4: LLVM lib as default

- LLVM lib becomes default for release builds (`build --release`)
- Cranelift remains default for debug builds (`build`)
- C backend remains as portable fallback

---

## Related Documents

- [`backend_default_decision.md`](backend_default_decision.md) — Decision doc for LLVM as default
- [`backend_complete_summary.md`](backend_complete_summary.md) — Backend completion tracking
- [`backend_shared_architecture.md`](backend_shared_architecture.md) — Shared backend infrastructure
- [`backend_production_plan.md`](backend_production_plan.md) — Production readiness plan
- [`gpu_backend_design.md`](gpu_backend_design.md) — GPU backend design (CUDA/Vulkan)
- [`vhdl_backend_design.md`](vhdl_backend_design.md) — VHDL synthesis backend
