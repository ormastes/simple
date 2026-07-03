# Test Specification Index

*Curated lane index: Linux RenderDoc/Vulkan, Engine2D, GUI Vulkan window, Breakout, and SimpleOS LLVM evidence.*

## Quick Stats

- **Total Features:** 10
- **Complete Documentation:** 10 (100%)
- **Stubs Remaining:** 0
- **Total Lines:** 3694
- **Warnings:** tracked in individual generated manuals

---

## GPU / Engine2D

| Feature | Status | Tests | Details |
|---------|--------|------:|---------|
| [Vulkan Compute Oracle](01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.md) | Complete | 7 | 420 lines |
| [Engine2D Facade Backend Mutation](test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.md) | Complete | 5 | 266 lines |
| [Web Renderer Backend Parity](test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.md) | Complete | 10 | 236 lines |

## GUI Vulkan

| Feature | Status | Tests | Details |
|---------|--------|------:|---------|
| [GUI Vulkan Window Verification](test/03_system/check/gui_vulkan_window_spec.md) | Complete | 6 | 272 lines |

## Game2D Breakout

| Feature | Status | Tests | Details |
|---------|--------|------:|---------|
| [Breakout Production Readiness](test/03_system/game2d/breakout_production_spec.md) | Complete | 1 | 146 lines |
| [Breakout Render Oracles](test/03_system/game2d/breakout_render_oracles_spec.md) | Complete | 2 | 167 lines |
| [Breakout Milestone Captures](test/03_system/game2d/breakout_captures_spec.md) | Complete | 1 | 172 lines |
| [Breakout Window Capture](test/03_system/game2d/breakout_window_capture_spec.md) | Complete | 1 | 156 lines |

## SimpleOS LLVM Port

| Feature | Status | Tests | Details |
|---------|--------|------:|---------|
| [Per Target Build](02_integration/os/port/llvm/per_target_build_spec.md) | Complete | 59 | 1612 lines |
| [Smoke Clang](02_integration/os/port/llvm/smoke_clang_spec.md) | Complete | 7 | 247 lines |
