# Audit: LLVM Backend Support

**Date:** 2026-04-04
**Feature:** LLVM backend compilation and linking

## Implemented Core

Two self-hosted LLVM backends + Rust bootstrap backend:

**1. Llvm (CLI-based, `BackendKind.Llvm`)**
- MIR-to-LLVM-IR textual generation: `src/compiler/70.backend/backend/mir_to_llvm.spl`
- IR builder: `src/compiler/70.backend/backend/llvm_ir_builder.spl`
- 15 optimization passes: `src/compiler/70.backend/backend/llvm_passes.spl`
- 8 architecture targets + OS detection: `src/compiler/70.backend/backend/llvm_target.spl`
- Codegen adapter: `src/compiler/70.backend/backend/llvm_codegen_adapter.spl`
- Native link orchestrator: `src/compiler/70.backend/backend/llvm_native_link.spl`

**2. LlvmLib (C API, `BackendKind.LlvmLib`)**
- ~120 LLVM C API bindings via `DynLib`: `src/lib/nogc_sync_mut/ffi/llvm.spl`
- In-process IR generation + passes + emit: `src/compiler/70.backend/backend/llvm_lib_backend.spl`
- Translation: `llvm_lib_translate.spl`, `llvm_lib_translate_expr.spl`

**3. Rust bootstrap (`inkwell` v0.5, LLVM 18)**
- ~20 source files: `src/compiler_rust/compiler/src/codegen/llvm/`
- 10+ test files: `src/compiler_rust/compiler/src/codegen/llvm_tests/`

**Auto-selection** (`backend_helpers.spl:196-202`): LlvmLib > Llvm > Cranelift

## Support Matrix

| Capability | Llvm (llc CLI) | LlvmLib (C API) | Rust/inkwell |
|---|---|---|---|
| x86_64 | Yes | Yes | Yes |
| i686 | Yes | Yes | Yes |
| AArch64 | Yes (cross) | Yes | Yes |
| ARMv7 | Yes (cross) | Yes | Yes |
| RISC-V 32/64 | Yes (cross) | Yes | Yes |
| WASM32/64 | Yes (wasm-ld) | Via target | Yes |
| Bare-metal | Yes | Yes | Unknown |
| Optimization | opt CLI (O0-O3) | LLVMRunPasses | inkwell OptLevel |
| GPU/CUDA | N/A | N/A | `llvm-gpu` feature |
| Native linking | clang/gcc/ld | Yes | Yes |

## External Dependencies

- **Llvm backend:** `llc` (16-18 fallback chain), `opt`, `clang`, `nm`, `wasm-ld`/`wasm-opt` (WASM only)
- **LlvmLib backend:** `libLLVM-18.so` (or equivalent) -- no CLI tools
- **Rust bootstrap:** LLVM 18 dev libraries at compile time

## Known Limits

1. LLVM version hardcoded to 16-18 range; no 19+ support verified
2. Windows `llc_available()` uses Unix `command -v` (needs `where` for Windows)
3. Cross-compilation requires target sysroot and linker
4. GPU only through Rust bootstrap (`llvm-gpu` feature)
5. Tests run in interpreter mode (file-load verification only)

## Proof References

**Self-hosted:** 20 `.spl` files in `src/compiler/70.backend/backend/llvm_*`
**Rust bootstrap:** 20 `.rs` files in `src/compiler_rust/compiler/src/codegen/llvm/`
**FFI bindings:** `src/lib/nogc_sync_mut/ffi/llvm.spl`
**Tests:** 126 total across 10 spec files (`llvm_backend_spec.spl` 32, `llvm_backend_e2e_spec.spl` 26, `backend_llvm_1_spec.spl` 15, arch-specific specs 46, native_link 4, ir_builder 3)

## Recommended README Wording

> **LLVM backend** -- Two modes: in-process via `libLLVM` C API (preferred, no external tools) or CLI-based via `llc`/`opt` (LLVM 16-18); supports x86_64, i686, AArch64, ARMv7, RISC-V 32/64, WASM32/64, and bare-metal targets with full optimization pipeline and cross-compilation; auto-selects LlvmLib > Llvm > Cranelift based on host availability
