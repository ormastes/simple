# Implemented Qualified Features -- Parallel Audit Summary

**Date:** 2026-04-04
**Plan:** `doc/03_plan/agent_tasks/implemented_qualified_features_parallel_audit.md`

## Merged Summary Table

| Feature | Implemented Core | Known Limits | Proof References | Recommended README Wording |
|---------|-----------------|--------------|------------------|---------------------------|
| **Math blocks** (`m{}`, `loss{}`, `nograd{}`) | Parser (Rust + Simple), block registry, HIR resolve, MIR lowering, rendering library (5 formats), VSCode extension (concealment + hover + panel), Neovim plugin (extmarks + float), treesitter highlighting | `loss{}` calls `rt_torch_autograd_backward`; `nograd{}` uses balanced begin/end with failure-safe MIR patching + RAII `NogradGuard`; codegen returns unit for custom blocks; no derivative/limit LaTeX nodes | 15.blocks (3 defs), 35.semantics (resolve + safety), 50.mir (lowering), math_repr.spl, VSCode math/ (4 files), nvim math.lua, 6 spec files (28+ tests) | Math blocks (`m{}`, `loss{}`, `nograd{}`) -- inline DSL with `^` power, `'` transpose, implicit multiplication, broadcast operators, and `@` matrix multiply; renders to LaTeX and Unicode in VSCode and Neovim; `loss{}` triggers auto-backward on torch backend; `nograd{}` provides failure-safe gradient suppression with RAII guard |
| **LLVM backend** | Two self-hosted backends (CLI via `llc`/`opt`, in-process via `libLLVM` C API) + Rust bootstrap (`inkwell`); 8 arch targets; auto-selection (LlvmLib > Llvm > Cranelift); 15 opt passes | LLVM 16-18 only; Windows tool discovery uses Unix `command -v`; cross-compilation needs target sysroot; GPU only via Rust bootstrap | 20 `.spl` backend files, 20 `.rs` bootstrap files, ~120 FFI bindings, 126 tests across 10 spec files | LLVM backend -- two modes: in-process via `libLLVM` C API (preferred) or CLI-based via `llc`/`opt` (LLVM 16-18); supports x86_64, i686, AArch64, ARMv7, RISC-V 32/64, WASM32/64, and bare-metal; auto-selects based on host availability |
| **Runtime families** (GC / no-GC) | Six stdlib tiers by memory/concurrency contract; compiler `GcMode`/`GcConfig` with boundary warnings; MIR borrow/escape/barrier analysis; per-target `no_gc`/`no_std` presets | Interpreter doesn't enforce GcMode; gc_async_mut smallest (45 files, GPU only); nogc_async_immut has 0 test files; `@no_gc` attribute unused in stdlib; C runtime has no GC (GC is in Simple) | gc_config.spl, gc_boundary.spl, 55.borrow/ (8 files), target_presets.spl, gc.spl, 223 GC specs, 20 borrow specs, 41 baremetal specs | Runtime families -- six stdlib tiers with compiler-enforced GC boundary warnings, MIR-level borrow/escape/barrier analysis, and per-target `no_gc`/`no_std` presets for embedded cross-compilation |
| **Shared UI testing** | `UITestClient` (HTTP protocol), shared `handle_test_request` handler, integrated by web backend + TUI-web proxy | Shared = web + tui_web only (11 other surfaces excluded); HTTP-level only (no pixel/layout testing); requires compiled mode | ui_test/ (4 source files), test_api/ (handler + json), unified_test_spec.spl (both servers), 4 spec files (21 tests) | Shared UI test client (`std.ui_test`) -- HTTP-based protocol with shared handler for web backend and TUI-web proxy; unified spec verifies equivalent behavior through the same API |
| **Remote baremetal** | 6 adapters (QEMU RV32/ARM, GHDL, CH32V307, STM32H7, TRACE32); complete compile-upload-execute-collect pipeline; 6-arch assembly startup; baremetal build system | All tests interpreter-mode only; every lane needs external tools; GHDL partial (semihost only); ZedBoard FPGA incomplete (JTAG not connected); hardware lanes skip when absent | remote/exec/ (6 adapters + manager), baremetal.spl, startup/ (6 arch), 2 verification reports (PASS), multiple E2E specs | Bare-metal and remote execution -- cross-compile to ARM, RISC-V, x86_64 baremetal with QEMU testing; remote JIT via GDB-MI, OpenOCD, `wlink`, GHDL, TRACE32 -- hardware lanes skip when probes absent |

## Qualification Assessment

All five features are **correctly qualified as "implemented with qualifiers"**:

1. **Math blocks**: Syntax, parsing, rendering, editor tooling, and autograd runtime are solid. `loss{}` emits real backward calls; `nograd{}` has failure-safe gradient suppression. Qualify with "torch backend required for gradient features."
2. **LLVM backend**: Substantive (two backends, 8 targets, auto-selection). Qualify with LLVM version range and cross-compilation sysroot dependency.
3. **Runtime families**: Architecture is real (6 tiers, compiler enforcement). Qualify with interpreter non-enforcement and small gc_async_mut/nogc_async_immut coverage.
4. **Shared UI testing**: Genuine shared testing across 2 surfaces. Qualify as "web + TUI-web only" -- do NOT claim unified UI layer.
5. **Remote baremetal**: Real execution lanes proven on live hardware. Qualify with board/tool dependencies and FPGA incompleteness.

No feature should be upgraded to "fully complete." No feature should be downgraded to "experimental" -- all have working implementations with source evidence.

## Individual Audit Reports

- [`audit_math_blocks_2026-04-04.md`](audit_math_blocks_2026-04-04.md)
- [`audit_llvm_backend_2026-04-04.md`](audit_llvm_backend_2026-04-04.md)
- [`audit_runtime_families_2026-04-04.md`](audit_runtime_families_2026-04-04.md)
- [`audit_shared_ui_testing_2026-04-04.md`](audit_shared_ui_testing_2026-04-04.md)
- [`audit_remote_baremetal_2026-04-04.md`](audit_remote_baremetal_2026-04-04.md)
