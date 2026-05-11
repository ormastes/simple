# Remaining Roadmap

**Generated:** 2026-05-10
**Source:** Consolidated from 98 session plans (now deleted)

---

## 1. 3D Engine GPU Acceleration + WebGPU (DONE)

**Priority:** P1
**Status:** Landed 2026-05-10
**Commits:** `42c86a87d2` (impl+refactor), `fe32384f50` (verify+spec-fix)

### Delivered
- `RenderBackend3D` trait with `SoftwareRenderBackend3D`, `VulkanRenderBackend3D`, `WebGpuRenderBackend3D` implementations
- `AnyRenderBackend3D` tagged enum for Engine3D polymorphism (no trait objects)
- `RenderCapability3D` struct + `detect_best_backend_3d()` auto-detection
- GPU mesh pipeline: `gpu_mesh_upload` / `gpu_mesh_draw` via backend trait
- GPU lighting: `LightUniform` / `GpuLightingState` uniform buffer management
- Shader cross-compilation: `ShaderCompiler` with GLSL→SPIR-V (Vulkan) + GLSL→WGSL (WebGPU) + cache
- WebGPU shim: 21 `rt_wgpu_3d_*` externs + 19 `rt_vulkan_*_graphics` externs declared
- 3D texture system: `TextureCache3D` + `TextureAtlas3D` + `material_bind`
- MDSOC+ audit clean: no business-layer imports of render backends
- `ForwardRenderer3D` preserved as software fallback via composition
- 14 new files, 2,529 lines; 7 spec files, 82 passing / 64 failing (extern stubs)

### Follow-ups
- Register `rt_vulkan_*_graphics` and `rt_wgpu_3d_*` externs in `signatures.rs` for interpreter mode
- `fn method(self)` self-mutation pattern needs compiler support or value-return refactor

---

## 2. LLVM/Rust/Simple Self-Host in SimpleOS (ELF SYMTAB FIXED)

**Priority:** P0
**Status:** ELF bug fixed 2026-05-10; self-host integration remaining
**Commits:** `common_backend.rs` Preemptible→Export fix; `cranelift.rs` reemit_clean_macho weak-scope fix

### Fixed
- **Root cause:** `common_backend.rs` used `Linkage::Preemptible` for all defined functions → cranelift-object emitted all symbols as `STB_WEAK` → linker couldn't distinguish app symbols from crt0 stubs → `freestanding_weak_boot_defsyms` found no STRONG defs
- **Fix A:** `Linkage::Preemptible` → `Linkage::Export` (lines 538, 548) — all symbols now `STB_GLOBAL`
- **Fix B:** `reemit_clean_macho` weak symbols with `SymbolScope::Compilation` promoted to `Linkage` — prevents weak-in-LOCAL partition on re-emitted objects

### Remaining (self-host integration)
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
| 1 | 3D Engine GPU + WebGPU | Done | — |
| 2 | LLVM/Rust Self-Host in SimpleOS | P0 | ELF fixed; integration remaining |
| 3 | Driver Framework compiler work | P2 | Compiler infra |
| 4 | Editor/IDE Platform | P2 | None |
| 5 | DL + GPU Stack | Done | — |
