# Remaining Roadmap

**Generated:** 2026-05-10
**Source:** Consolidated from 98 session plans (now deleted)

---

## 1. 3D Engine GPU Acceleration + WebGPU

**Priority:** P1
**Status:** Planning (not started)
**Date planned:** 2026-05-09

### Scope
- Refactor CPU-based 3D engine (`src/lib/nogc_sync_mut/engine/`) for GPU acceleration
- MDSOC+ consistency audit (align with 2D engine patterns)
- API consistency between 2D and 3D engines
- Browser WebGPU backend support
- 3D texture system

### Key Files
- `src/lib/nogc_sync_mut/engine/core/engine3d.spl` (191 lines)
- `src/lib/nogc_sync_mut/engine/render/renderer3d.spl` (556 lines)
- `src/os/ml/gpu_tensor.spl` (GPU tensor ops — can share kernel infrastructure)

### Deliverables
1. MDSOC+ audit of 3D engine components
2. Unified RenderBackend3D trait (Vulkan + WebGPU + software fallback)
3. GPU-accelerated mesh transforms + lighting
4. WebGPU shim for browser target
5. 3D texture atlas + material system

---

## 2. LLVM/Rust/Simple Self-Host in SimpleOS

**Priority:** P0 (blocked)
**Status:** Blocked on BUG-COMPILER-ELF-SYMTAB
**Date planned:** 2026-04-28

### Blocker
ELF SYMTAB bug: Cranelift emitter places WEAK-binding symbols in LOCAL portion of symbol table, violating `sh_info` invariant. `ld.lld` rejects the output.

### Root Cause (narrowed)
- `src/compiler_rust/compiler/src/codegen/cranelift.rs` — symbol emission treats weak boot-aliases as LOCAL
- Likely regression between Apr 27–28 commits touching symbol binding

### Fix Steps
1. Bisect: `git bisect` on `src/compiler_rust/` between known-good and broken commits
2. Fix: ensure `LinkageWeak` maps to `SymbolBinding::Weak` (not Local) in cranelift codegen
3. Rebuild compiler + kernel ELF
4. Verify: `native-build` exits 0, ELF loads in SimpleOS

### Success Criteria
- clang, rustc, and `simple` all run as file-loadable apps inside SimpleOS
- Closed self-host bootstrap: SimpleOS can compile itself

---

## 3. Driver Framework — Compiler Follow-ups

**Priority:** P2
**Status:** Framework landed (A–E), compiler work remaining
**Date landed:** 2026-04-18

### Already Done
- Phase A: `Driver` trait + types + error + design + author guide
- Phase B: manifest, registry, static_table, loader + test
- Phase C.1: DMA API + barrier-only fallbacks + test
- Phase D: fs/gpu adapters + native_libs
- Phase E: null_block example driver + test
- Cranelift `>>` interim fix for signed narrow ints

### Remaining
1. **C.2 — Cranelift `>>` proper fix**: Full right-shift semantics for all widths (var-load, param, call-ret paths)
2. **C.3 — Bitfield sugar**: Compiler frontend support for packed bitfield struct declarations (needed for hardware register maps)

---

## 4. Editor / IDE Platform

**Priority:** P2
**Status:** Partially implemented (SVIM TUI v1), VSCode designed
**Date audited:** 2026-05-10

### Current State
- **SVIM TUI** (`src/app/svim/`): v1 foundation complete — modal editing, buffer management, syntax highlighting
- **VSCode Extension** (`src/app/vscode_extension/`): Architecture designed, minimal code. TypeScript infrastructure + test workspace exist.

### Remaining
1. SVIM TUI: multi-buffer, split panes, LSP integration, plugin system
2. VSCode Extension: implement language server client, diagnostics, code actions, debugging
3. Unified editor backend shared between SVIM and VSCode

---

## 5. DL + GPU Compute Stack (DONE)

**Priority:** Completed
**Status:** Landed 2026-05-10
**Commit:** `cb57337` (main)

Delivered `src/os/ml/` — 7 files: kernels, gpu_tensor, autograd, optimizer, data, model, __init__. Bridges existing CUDA FFI to high-level DL abstractions (training + inference + serialization).

---

## Summary

| # | Item | Priority | Blocker |
|---|------|----------|---------|
| 1 | 3D Engine GPU + WebGPU | P1 | None |
| 2 | LLVM/Rust Self-Host in SimpleOS | P0 | ELF SYMTAB bug |
| 3 | Driver Framework compiler work | P2 | Compiler infra |
| 4 | Editor/IDE Platform | P2 | None |
| 5 | DL + GPU Stack | Done | — |
