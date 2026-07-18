# GPU Rendering Tests Map

**Quick Reference**: All GPU rendering validation tests in the Simple compiler codebase.

> **Note**: This guide exists to prevent GPU rendering tests from being missed or recreated. If adding new GPU features, reference this map first.
>
> ⚠️ **IMPORTANT:** See `doc/07_guide/testing/gpu_rendering_tests_gap_analysis.md` for honest coverage assessment. **Most tests are validation/audit focused, not functional.** Current Linux evidence has Simple/Chrome/Electron RenderDoc `.rdc` artifacts with `RDOC` magic in `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`; remaining platform gaps include Metal logs (macOS-only), DirectX logs (Windows-only), and broader GUI item combinations.

## Test Category Legend

| Symbol | Meaning |
|--------|---------|
| ✅ | Functional test; actually captures and compares real data |
| ⚠️ | Partial; validates infrastructure but not fully functional |
| ❌ | Audit/validation only; validates evidence presence, not actual rendering |

## Newly Implemented Functional Tests (test/03_system/check/)

### GPU Rendering Functional Tests (NEW)

| Test | Coverage | Status |
|------|----------|--------|
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl` | Public Engine2D facade mutation/readback for software + CPU SIMD, including clip/mask through image, scaled image, and transformed image | ✅ 8 tests passing — real facade `read_pixels()` assertions |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl` | Vulkan clear/rect/draw_image device readback, clipped draw_image, clip rect, mask, and cross-backend wrappers | ✅ 7 tests passing — Vulkan-backed readback oracle |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl` | CPU, CPU SIMD, Metal-on-Vulkan, CUDA fallback, OpenCL fallback, and Vulkan generic layout parity | ✅ 10 tests passing — backend selection parity |
| `gpu_rendering_functional_cpu_simd_coverage_spec.spl` | Real pixel capture, deterministic rendering, render stats, event patterns, multi-item rendering | ✅ 9 tests passing — real SoftwareRenderer.get_pixels() pixel capture |
| `gpu_rendering_vulkan_renderdoc_capture_spec.spl` | Trace structure, metrics validation, CPU-Vulkan parity, draw call alignment | ✅ 5 tests passing — RenderDoc trace validation framework |
| `gpu_rendering_renderdoc_capture_functional_spec.spl` | Render log capture, CPU-Vulkan alignment, perfect match/mismatch detection, threshold validation, combined image+log comparison | ✅ 8 tests passing — RenderLogCapture class with alignment_percentage() |

### Electron/Chrome Web Rendering + RenderDoc (Prior)

| Test | Coverage | Status |
|------|----------|--------|
| `electron_simple_web_engine2d_proof_validator_spec.spl` | Web rendering, Engine2D, ARGB pixel capture, checksum validation | ⚠️ 22 tests passing — validates proof format, not real rendering |
| `electron_html_compat_geometry_simple_bin_spec.spl` | HTML geometry compat, Electron layout | ⚠️ Existing — no image comparison |
| `electron_generated_gui_web_proof_validator_spec.spl` | Generated GUI + web proof validation | ⚠️ Existing — audit only |
| `electron_vulkan_web_parity_windows_simple_bin_spec.spl` | Vulkan-backed web rendering (Windows) | ⚠️ Existing — perf only, no cross-backend comparison |
| `electron_simple_web_layout_proof_validator_spec.spl` | Layout manifest validation | ❌ Audit only |
| `electron_simple_web_layout_manifest_evidence_spec.spl` | Layout evidence presence | ❌ Audit only |
| `electron_live_smoke_proof_validator_spec.spl` | Live capture smoke test | ⚠️ Basic validation |
| `electron_mdi_proof_validator_spec.spl` | MDI window proof validation | ❌ Audit only |
| `electron_mdi_simple_bin_spec.spl` | MDI rendering binary | ⚠️ Existing |

### GUI RenderDoc & Metal Integration

| Test | Coverage | Status |
|------|----------|--------|
| `gui_renderdoc_aggregate_autodiscovery_spec.spl` | RenderDoc capture discovery | ❌ Audit only — checks evidence file presence |
| `gui_renderdoc_aggregate_cache_modes_spec.spl` | RenderDoc cache optimization | ❌ Audit only — cache behavior validation |
| `gui_renderdoc_feature_coverage_fast_gate_spec.spl` | RenderDoc feature gates (fast path) | ❌ Audit only — gate validation |
| `gui_renderdoc_feature_coverage_status_spec.spl` | RenderDoc coverage status validation | ❌ Audit only — use `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md` for current Linux `.rdc` completion; Metal/DirectX remain platform-specific |
| `gui_color_image_pipeline_8k_simple_bin_spec.spl` | 8K GUI color/image pipeline | ⚠️ Perf measurement only |
| `gtk_gui_size_speed_simple_binary_spec.spl` | GTK GUI rendering (Linux) | ⚠️ Perf measurement only |
| `gui_retained_perf_source_freshness_spec.spl` | Perf source artifact freshness | ❌ Audit only |
| `gui_showcase_perf_alias_runtime_contract_spec.spl` | Perf contract validation | ❌ Audit only |
| `gui_showcase_perf_artifact_provenance_contract_spec.spl` | Artifact provenance validation | ❌ Audit only |
| `gui_showcase_perf_backend_contract_spec.spl` | Backend perf contract | ❌ Audit only |
| `gui_hardening_open_gates_simple_bin_spec.spl` | Security hardening gates | ⚠️ Existing |

## Unit-Level Tests (test/01_unit/)

### Vulkan Backend (nogc_sync_mut)

| Test | Coverage | Status |
|------|----------|--------|
| `test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl` | Vulkan 3D rendering pipeline | ✅ 16 tests passing — functional 3D backend tests |
| `test/01_unit/lib/nogc_sync_mut/engine/render/backend3d_spec.spl` | Generic 3D backend abstraction | ✅ 10 tests passing — abstract interface tests |
| `test/01_unit/lib/nogc_sync_mut/engine/render/software_backend3d_negative_offset_guard_spec.spl` | Software 3D rendering guardrails | ✅ Guardrail validation |
| `test/01_unit/lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl` | WebGPU backend validation | ⚠️ Existing — API validation |

### Direct3D/DXVK Integration (gc_async_mut & nogc_async_mut)

| Test | Coverage | Status |
|------|----------|--------|
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl` | Direct3D Engine2D rendering | ⚠️ Existing — unit-level API tests |
| `test/01_unit/lib/nogc_async_mut/gpu/vkd3d_d3d12_spec.spl` | VKD3D D3D12 compatibility | ⚠️ Existing — translation layer tests |
| `test/01_unit/lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl` | DXVK/VKD3D dispatch | ⚠️ Existing — dispatch routing tests |
| `test/01_unit/lib/nogc_async_mut/gpu/dxvk_d3d10_icd_spec.spl` | DXVK D3D10 ICD layer | ⚠️ Existing — ICD compatibility |

## Key Infrastructure Files

### GPU Rendering Validation Libraries
```
src/lib/common/gpu/gui_render_validation.spl      # Phase 6 HTML/CSS→DrawIr validation (14 functions)
src/lib/common/ui/draw_ir.spl                     # Simple 2D abstraction (structured commands)
src/lib/common/image/image_diff.spl               # ARGB pixel comparison with tolerance
src/lib/common/renderdoc/renderdoc_diff.spl       # Vulkan trace comparison (not yet wired)
src/lib/common/gpu/direct_render_log_compare.spl  # Cross-backend comparison (not yet wired)
```

**Status:** Infrastructure exists ✅ but most functions not yet called from functional tests.

### GPU Backend Source Code
```
src/compiler/70.backend/backend/vulkan_backend.spl
src/compiler/70.backend/backend/cuda_backend.spl
src/compiler/70.backend/backend/directx/...
src/lib/nogc_sync_mut/engine/render/vulkan_backend.spl
src/lib/gc_async_mut/gpu/engine2d/directx_backend.spl
```

## Documentation

### Guides
- **GPU Rendering Tests Gap Analysis:** `doc/07_guide/testing/gpu_rendering_tests_gap_analysis.md` — **READ THIS FIRST**
- **RenderDoc Capture Infrastructure:** `doc/07_guide/tooling/renderdoc_capture_infra.md`
- **Current Linux RenderDoc + SimpleOS hardening evidence:** `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
- **SPipe Test Template:** `.claude/templates/spipe_template.spl` (includes GPU rendering examples)

### Plans
- **Full GPU Render Offload Strategy:** `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`
- **Vulkan-Backed Web/GUI RenderDoc:** `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`

### Bug Tracking (Critical Blockers)
- **RenderDoc Blockers:** `doc/08_tracking/bug/gui_web_2d_vulkan_renderdoc_blockers_2026-06-23.md`
- **Electron RenderDoc Diagnostics:** `doc/08_tracking/bug/electron_renderdoc_vulkan_widget_capture_launch_diagnostics_2026-06-28.md`
- **GUI RenderDoc Performance:** `doc/08_tracking/bug/gui_renderdoc_aggregate_spec_static_cache_artifact_bloat_2026-06-27.md`

## Coverage Summary

| Aspect | Count | Status | Implementation |
|--------|-------|--------|-----------------|
| **Total GPU tests** | 73+ | ✅ Passing | Engine2D 2D backend evidence + 22 functional + 26 prior validation |
| **CPU SIMD tests** | 9 | ✅ Functional | Real SoftwareRenderer pixel capture, deterministic rendering |
| **RenderDoc tests** | 13 | ✅ Functional | Trace structure, CPU-Vulkan alignment, perfect match detection |
| **Vulkan 3D tests** | 16+ | ✅ Functional | 3D only, no 2D GUI items |
| **Direct3D tests** | 6+ | ⚠️ Unit-level | VKD3D/DXVK translation layer, not GUI rendering |
| **Web rendering tests** | 22 | ⚠️ Validator | Proof format validation, not real rendering |
| **Event handling pattern** | ✅ | ✅ Documented | Render-before → clear → re-render → verify pattern |
| **RenderLog comparison** | ✅ | ✅ Implemented | alignment_percentage() method with 90% threshold |
| **Metal render log tests** | 0 | ❌ Environmental | Unavailable (requires macOS GPU) |
| **DirectX render log tests** | 0 | ❌ Environmental | Unavailable (requires Windows GPU) |
| **GUI item combinations** | ✅ | ✅ Tested | Buttons, forms, containers, text fields in SIMD tests |
| **GPU backends** | 5 | ✅ Implemented | Vulkan, Metal, DirectX, CUDA, HIP |

## Running GPU Rendering Tests

### All GPU tests:
```bash
bin/simple test test/03_system/check/electron*.spl test/03_system/check/gui*.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/engine/render/*backend3d*.spl
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx*.spl
```

### By category:
```bash
# Vulkan (functional)
bin/simple test test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl

# Direct3D (unit-level)
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl

# Web rendering validation
bin/simple test test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl

# Feature audit (checks evidence availability, not actual rendering)
bin/simple test test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl
```

### Note on Test Limitations

- **Interpreter-only:** Many tests run in interpreter mode, which limits execution scope
- **Mock data:** Web rendering validator uses synthetic ARGB, not real captures
- **Audit vs Functional:** Most GUI tests are compliance audits (evidence presence), not functional tests
- **Event handling:** No actual click, keyboard, or pointer event tests exist yet

## Adding New GPU Rendering Tests

When adding GPU validation tests, reference:
1. **Gap Analysis:** `doc/07_guide/testing/gpu_rendering_tests_gap_analysis.md` — understand what's missing
2. **Template:** `.claude/templates/spipe_template.spl` (GPU rendering section)
3. **Existing Patterns:**
   - Web rendering baseline: `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl`
   - 3D backend tests: `test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl`
   - Validation infrastructure: `src/lib/common/gpu/gui_render_validation.spl`

**Standard structure for NEW functional tests**:
- Real pixel capture (not mock JSON)
- Event handling (click, keyboard, state changes)
- Cross-backend comparison (CPU vs Vulkan vs Metal vs DirectX)
- RenderDoc/Metal/DirectX trace validation
- Image-based + render-log-based comparison
- Multiple GUI item types (not single test scene)

---

**Last verified:** 2026-07-01  
**Next review:** When implementing event handling or RenderDoc capture
