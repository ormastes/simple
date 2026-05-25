# Remaining Roadmap

**Generated:** 2026-05-10
**Source:** Consolidated from 98 session plans (now deleted)

---

## 0. Crash Recovery Replan - Active

**Priority:** P0
**Status:** Active as of 2026-05-25
**Plan:** [`crash_recovery_replan_2026-05-25.md`](crash_recovery_replan_2026-05-25.md)

### Scope
- Remove dummy/fallback pass paths from SimpleOS QEMU checks and make the
  board lane runnable on real hardware.
- Optimize Simple FAT until it beats the C FAT path on representative
  filesystem workloads.
- Optimize NVFS and DBFS until both beat the optimized FAT path for executable
  load, metadata, write, and recovery workloads.
- Continue optimization plugin work with measured native/MIR specialization
  wins.
- Improve SimpleQ plus embedded/full Simple DB with executor-backed indexes and
  benchmark gates.

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

## 2. LLVM/Rust/Simple Self-Host in SimpleOS (DONE)

**Priority:** P0
**Status:** Landed 2026-05-11
**Commits:** ELF SYMTAB fix (2026-05-10), self-host integration (2026-05-11)

### Delivered
- **ELF fix:** `Linkage::Preemptible` → `Export` + `reemit_clean_macho` weak-scope promotion
- **Capability bug fix:** `CapabilitySet.full()` was producing empty caps — FileRead/FileWrite/FileCreate/FileExec/ProcessSpawn now seeded for full-capability tasks
- **Build script:** `scripts/simpleos-native-build.shs` — builds Simple compiler as static SimpleOS ELF (x86_64/riscv64/aarch64)
- **Initramfs:** Compiler packed at `/bin/simple` + `/usr/bin/simple`
- **QEMU integration test:** `test/integration/simpleos_self_host_spec.spl` (14 cases) + kernel smoke step + e2e verify
- **Self-host chain:** SimpleOS boots → loads compiler from initramfs → compiles .spl → runs output

### Follow-ups
- clang/rustc cross-compilation as static SimpleOS executables (external toolchain build)
- User-process exec support for full end-to-end QEMU verification

---

## 3. Driver Framework — Compiler Follow-ups (DONE)

**Priority:** P2
**Status:** All items complete 2026-05-11
**Date landed:** 2026-04-18

### Already Done
- Phase A: `Driver` trait + types + error + design + author guide
- Phase B: manifest, registry, static_table, loader + test
- Phase C.1: DMA API + barrier-only fallbacks + test
- Phase D: fs/gpu adapters + native_libs
- Phase E: null_block example driver + test
- Cranelift `>>` interim fix for signed narrow ints

### Remaining
1. ~~**C.2 — Cranelift `>>` proper fix**~~: Done 2026-05-11. LLVM backend now dispatches signed (ashr) vs unsigned (lshr) right-shift. Cranelift paths verified already correct. Follow-up: wire vreg_types into LLVM call sites for unsigned shift accuracy.
2. ~~**C.3 — Bitfield sugar**~~: Already implemented. Parser (`parse_bitfield_decl`), AST (`BitfieldDef`), HIR (`HirType::Bitfield`), type registration, constructor lowering all in place. Driver adoption pending.

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
| 2 | LLVM/Rust Self-Host in SimpleOS | Done | — |
| 3 | Driver Framework compiler work | Done | — |
| 4 | Editor/IDE Platform | P2 | None |
| 5 | DL + GPU Stack | Done | — |
