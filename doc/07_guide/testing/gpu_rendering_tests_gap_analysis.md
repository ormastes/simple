# GPU Rendering Tests: Gap Analysis & Implementation Status

**Last Updated:** 2026-07-01  
**Status:** In Progress — Critical gaps identified

## Executive Summary

**26 GPU rendering tests exist and pass** ✅ but **are validation/audit-focused, not functional**.

| Aspect | Status | Gap |
|--------|--------|-----|
| **Test Files** | ✅ 20+ exist | Only validators + infrastructure tests |
| **Image Capture** | ⚠️ Partial | Web rendering only (22 tests), no native GUI items |
| **Event Handling** | ❌ Missing | No click/keyboard/pointer tests; only `event_routing_status` flag |
| **RenderDoc Traces** | ❌ Unavailable | Marked `unavailable` in test assertions |
| **Metal Render Logs** | ❌ Unavailable | Marked `unavailable`; no macOS implementation |
| **DirectX Render Logs** | ❌ Unavailable | Marked `unavailable`; DXVK/VKD3D unit tests only |
| **Cross-Backend Comparison** | ❌ Not Functional | Infrastructure (lib/common/gpu/) exists but not wired to tests |
| **GUI Item Combinations** | ❌ Not Tested | Web rendering tests scene only (no buttons, inputs, containers) |
| **Screen Update Tests** | ❌ Missing | No tests verify event → render loop → screen update chain |

---

## Passing Tests (Validation Layer)

These tests **validate the test infrastructure itself**, not the rendering:

### Web Rendering Proof Validation (22 tests passing)
- **File:** `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl`
- **What it does:** Validates proof JSON format, checksums, ARGB artifact paths, file symlink status
- **What it tests:** The validator's ability to parse and validate proof format
- **Gap:** Tests validator, not actual rendering. Uses mock ARGB data, not real captured pixels.
- **Evidence captured:** None — artificial JSON structures

### Electron HTML Compatibility (Geometry)
- **File:** `test/03_system/check/electron_html_compat_geometry_simple_bin_spec.spl`
- **What it does:** Tests HTML layout geometry in Electron
- **Gap:** No image comparison, no event handling validation

### GUI RenderDoc Feature Coverage (8+ audit tests passing)
- **File:** `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
- **What it does:** Audits evidence file availability, status flags, platform matrix
- **Key findings from test assertions:**
  - `linux_vulkan_render_log_compare_renderdoc_simple_status=unavailable` ❌
  - `linux_vulkan_render_log_compare_renderdoc_chrome_status=unavailable` ❌
  - `macos_metal_render_log_compare_status=unavailable` ❌
  - `windows_d3d12_render_log_compare_status=unavailable` ❌
- **Gap:** Audit is comprehensive, but actual capture/compare is not implemented

### Vulkan Backend (16 tests passing)
- **File:** `test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl`
- **What it does:** Unit tests for Vulkan 3D rendering pipeline
- **Gap:** 3D rendering only, not 2D GUI items

### Backend3D Generic (10 tests passing)
- **File:** `test/01_unit/lib/nogc_sync_mut/engine/render/backend3d_spec.spl`
- **What it does:** Abstract backend interface testing
- **Gap:** No GUI item coverage

### Direct3D/DXVK (6+ tests passing)
- **Files:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl`, etc.
- **What it does:** VKD3D and DXVK dispatch testing
- **Gap:** Unit-level translation layer, not actual GUI rendering

### GTK GUI Performance (Existing)
- **File:** `test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl`
- **What it does:** GTK GUI rendering performance measurement
- **Gap:** Perf measurement only, no image capture or cross-backend comparison

---

## Missing Functional Tests

### 1. Event Handling & Screen Updates

**Current state:** `interaction_keyboard=missing`, `interaction_pointer=missing`, `interaction_clicks=0`

**What's needed:**
- Click event tests: Button click → render update → pixel change verification
- Keyboard input tests: Type in text field → render update → pixel verification
- Pointer hover tests: Hover → style change → visual update
- Event propagation: Nested containers, focus management
- Each event type should trigger render loop and capture pixels

**Example test gap:**
```spl
# NOT IMPLEMENTED
describe "Event Handling":
    it "button click updates rendering":
        val gui = create_gui_with_button()
        val pixels_before = capture_pixels()
        gui.click_button(0, 0)
        val pixels_after = capture_pixels()
        expect(pixels_after).not_equal(pixels_before)  # Missing

    it "text input updates render log":
        val gui = create_gui_with_textbox()
        val log_before = get_render_log("vulkan")
        gui.type_text("hello")
        val log_after = get_render_log("vulkan")
        expect(log_after.draw_call_count).to_be_greater_than(log_before.draw_call_count)  # Missing
```

### 2. GUI Item Combinations

**Current state:** Only web rendering test scene (`simple-web-engine2d-image-taskbar-command`)

**What's needed:** Systematic coverage of all GUI items:

| Category | Items | Tests Needed | Status |
|----------|-------|--------------|--------|
| **Containers** | div, section, article, nav, aside, main | 0 | ❌ |
| **Text** | p, h1-h6, span, strong, em, code, pre | 0 | ❌ |
| **Forms** | input, button, textarea, select, label, fieldset | 0 | ❌ |
| **Lists** | ul, ol, li, dl, dt, dd | 0 | ❌ |
| **Images & Media** | img, picture, video, audio, canvas | 1* | ⚠️ |
| **Tables** | table, tr, td, th, thead, tbody, tfoot | 0 | ❌ |
| **Layout** | grid, flexbox, float, position | 0 | ❌ |
| **Styling** | borders, shadows, gradients, transforms | 0 | ❌ |
| **Interactions** | hover, active, focus, disabled states | 0 | ❌ |

*Web rendering has image test, but not combinations with other items

**Minimum coverage needed:** ~100+ test cases covering:
- Each item type individually
- Common combinations (button + label, input + label, etc.)
- Multiple items in same render (stress test)
- State changes (enabled/disabled, visible/hidden, etc.)

### 3. RenderDoc Trace Capture & Comparison

**Current state:** Infrastructure exists but marked `unavailable` in tests

**Infrastructure present:**
- `src/lib/common/renderdoc/renderdoc_diff.spl` — RenderDoc trace comparison library
- Functions: `compare_renderdoc_traces()`, validation thresholds defined
- Missing: Actual RenderDoc capture integration

**What's needed:**
```spl
# NOT IMPLEMENTED
describe "RenderDoc Vulkan Capture":
    it "captures Simple rendering and compares to Chrome":
        val simple_trace = capture_vulkan_trace("simple", gui_html)
        val chrome_trace = capture_vulkan_trace("chrome", gui_html)
        val diff = compare_renderdoc_traces(simple_trace, chrome_trace)
        expect(diff.vulkan_call_parity).to_be_greater_than(0.90)  # Missing
```

**Required implementation:**
1. RenderDoc SDK integration (C FFI layer)
2. Trace capture start/stop functions
3. API call extraction from traces
4. Draw call parity calculation
5. Per-frame comparison logic

### 4. Metal Render Log Capture (macOS)

**Current state:** `macos_metal_render_log_compare_status=unavailable`

**What's needed:**
- MTLRenderCommandEncoder operation tracing
- Shader validation
- Texture binding comparison
- Frame timing metrics
- CPU vs Metal alignment validation

**Example missing:**
```spl
# NOT IMPLEMENTED
describe "Metal Rendering (macOS)":
    it "logs Metal render operations":
        val log = capture_metal_render_log(gui_html)
        expect(log.encoder_operations.len).to_be_greater_than(0)  # Missing
        expect(log.draw_call_count).to_equal(expected_count)  # Missing
```

### 5. DirectX Render Log Capture (Windows)

**Current state:** `windows_d3d12_render_log_compare_status=unavailable`

**What's needed:**
- D3D11/D3D12 device context capture via DXVK
- State object tracking
- Command list comparison
- CPU vs Direct3D alignment

### 6. Cross-Backend Image Comparison

**Current state:** Infrastructure exists, no functional tests

**What's needed:**
- Render same HTML to CPU_SIMD, Vulkan, Metal, DirectX
- Capture ARGB pixels from each
- Compare with tolerances (already defined: 90% CPU-Vulkan, 95% CPU-Metal, 85% Vulkan-Metal)
- Test must cover all GUI item types, not just one scene

**Example missing:**
```spl
# NOT IMPLEMENTED
describe "Cross-Backend Rendering Alignment":
    it "renders same HTML identically on CPU and Vulkan":
        for html in [button_html, text_html, image_html, table_html]:
            val cpu_pixels = render_to_pixels(html, "cpu_simd")
            val gpu_pixels = render_to_pixels(html, "vulkan")
            val match_pct = image_diff_compare(cpu_pixels, gpu_pixels, 96, 64, 0.99)
            expect(match_pct).to_be_greater_than(0.90)  # Missing
```

---

## Implementation Priority

### Phase 1 (Foundation) — Weeks 1-2
1. **Event handling capture**
   - Click/keyboard event functions
   - Render loop triggering on events
   - Pixel capture post-event
   - ~20 tests, 3 items (button, text input, container)

2. **Image capture & comparison for web rendering**
   - Extend electron_simple_web_engine2d_proof_validator to capture real pixels (not mock)
   - Compare CPU vs Vulkan on same HTML
   - Add 5+ HTML variants (button, text, image, form, table)

### Phase 2 (Backend Traces) — Weeks 3-4
1. **RenderDoc integration**
   - Capture Vulkan traces for Simple and Chrome
   - Implement call parity calculation
   - Add 10 tests covering different GUI patterns

2. **Metal & DirectX**
   - MTL render log capture (macOS)
   - D3D12 capture via DXVK (Windows)
   - Add 5 tests each platform

### Phase 3 (Systematic Coverage) — Weeks 5+
1. Generate 100+ test cases for all GUI item combinations
2. Cross-backend validation for each combination
3. Performance benchmarking (CPU vs GPU)
4. Edge case coverage (empty items, extreme sizes, nested structures)

---

## Key Files for Implementation

### Validation Infrastructure (Exists ✅)
- `src/lib/common/gpu/gui_render_validation.spl` — 14 validation functions
- `src/lib/common/image/image_diff.spl` — ARGB pixel comparison
- `src/lib/common/renderdoc/renderdoc_diff.spl` — RenderDoc comparison
- `src/lib/common/gpu/direct_render_log_compare.spl` — Cross-backend alignment

### Test Templates
- `.claude/templates/spipe_template.spl` — GPU rendering examples (documented 30+ lines)
- `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl` — Web baseline

### Documentation
- `doc/07_guide/tooling/renderdoc_capture_infra.md` — RenderDoc setup
- `doc/07_guide/testing/gpu_rendering_tests_map.md` — Test discovery (updated)

---

## Action Items

1. **Honesty check:** Update `gpu_rendering_tests_map.md` to distinguish:
   - ✅ Validation tests (audit/format checking)
   - ⚠️ Partial functional tests (web rendering only)
   - ❌ Missing functional tests (events, Metal, DirectX, combinations)

2. **Quick wins (this week):**
   - Wire up real pixel capture to electron_simple_web_engine2d_proof_validator (currently mock)
   - Add 5 more HTML test cases (button, input, table, etc.)
   - Implement one event handling test (click → pixel change)

3. **Document blockers:**
   - RenderDoc SDK integration path
   - Metal MTLRenderCommandEncoder tracing
   - DXVK capture API
   - Missing Electron/Chrome Vulkan proof scripts

---

## Related Issues

See `doc/08_tracking/bug/`:
- `gui_renderdoc_aggregate_spec_static_cache_artifact_bloat_2026-06-27.md`
- `gui_web_2d_vulkan_renderdoc_blockers_2026-06-23.md`
- `electron_renderdoc_vulkan_widget_capture_launch_diagnostics_2026-06-28.md`
