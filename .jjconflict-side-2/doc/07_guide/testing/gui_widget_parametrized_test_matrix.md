# GUI Widget Parametrized Test Matrix

**Date:** 2026-07-01  
**Status:** Test Strategy & Plan

## Executive Summary

**Test Coverage Matrix:**
- **47 Widget Types** × **8 Layout Algorithms** × **5 Design Systems** × **3 Device Classes** = **5,640 core tests**
- **With Orientations** (2): 11,280 tests
- **With Viewport Sizes** (3-4 per device): 16,920 - 22,560 tests

---

## Test Dimensions

### Dimension 1: Widget Types (47)

**Layout Containers (4):**
- Panel, Vbox, Hbox, Grid, Fixed

**Text & Labels (3):**
- Text, Label, Heading

**Forms & Input (6):**
- Input, Textfield, Textarea, Checkbox, RadioButton, Dropdown

**Navigation (7):**
- Tabs, TabBar, NavigationBar, Menubar, CommandBar, Sidebar, ContextMenu

**Data Display (3):**
- List, Table, Tree/Treenode

**Interactive (7):**
- Button, Switch, SegmentedControl, SearchBar, Progress, Scroll, Image

**Modals & Overlays (5):**
- Dialog, SheetModal, Tooltip, Toast, Divider

**Desktop/App Components (8):**
- CommandPalette, WorkspaceTabs, Inspector, UtilityRail, GlassTitleBar, Card, StatusChip, SelectionPill

**Accessibility (1):**
- EmptyState

### Dimension 2: Layout Algorithms (8)

| Algorithm | Test Focus |
|-----------|-----------|
| **Block** | Margin collapse, vertical stacking, width/height |
| **Inline** | Text flow, wrapping, baseline alignment |
| **Float** | Float positioning, clearance, content wrapping |
| **Table** | Cell sizing, spanning, alignment, borders |
| **Box Model** | Padding, margin, border, content box sizing |
| **Flex** | (implicit in core) - flex container/items |
| **Grid** | Grid tracks, spanning, auto-placement |
| **Paint** | Rendering order, z-index, clipping |

### Dimension 3: Design Systems (5)

| System | Platform | Use Case |
|--------|----------|----------|
| **Glass** | Windows 11, Fluent | Modern desktop UI |
| **iOS** | iOS, iPadOS | Apple touch UI |
| **TUI** | Terminal | Console applications |
| **Browser** | Electron, Chrome | Web/browser UI |
| **Office** | Office-like apps | Productivity tools |

### Dimension 4: Device Classes (3)

| Class | Breakpoint | Touch | Platform Examples |
|-------|-----------|-------|-------------------|
| **Phone** | < 600px (shortest-side) | Yes | iOS, Android phones |
| **Tablet** | ≥ 600px (shortest-side) | Yes | iPad, Android tablets |
| **Desktop** | 1024px+ | No | Windows, macOS, Linux |

### Dimension 5: Orientations (2) - Mobile Only

| Orientation | Viewport | Use Case |
|-------------|----------|----------|
| **Portrait** | 400×800 (phone), 600×960 (tablet) | Handheld primary |
| **Landscape** | 800×400 (phone), 960×600 (tablet) | Landscape mode |

### Dimension 6: Viewport Sizes (Per Device)

**Phone:**
- Small: 360×640 (old Android)
- Medium: 375×667 (iPhone 6/7/8)
- Large: 414×896 (iPhone XR/11)

**Tablet:**
- Small: 600×800 (older tablet)
- Medium: 768×1024 (iPad mini)
- Large: 1024×1366 (iPad Pro)

**Desktop:**
- Small: 1024×768 (netbook)
- Medium: 1440×900 (laptop)
- Large: 1920×1080 (desktop)

---

## Test Structure

### Core Test Matrix (5,640 tests)

```
for each widget in [47 widgets]:
  for each layout in [8 layouts]:
    for each design_system in [5 systems]:
      for each device_class in [3 classes]:
        test: widget_renders_correctly
        test: widget_interactive_handlers
        test: widget_accessibility_attributes
        test: widget_responsive_sizing
```

### Parametrized Test File Structure

**File:** `test/03_system/check/gui_widget_parametrized_rendering_spec.spl`

**Test Cases Per Widget:**

```spl
describe "GUI Widget Parametrized Rendering":
  # Matrix: 47 widgets × 8 layouts × 5 systems × 3 devices
  
  test_matrix = [
    {widget: Panel,      layout: Block,  system: Glass,   device: Desktop},
    {widget: Panel,      layout: Block,  system: Glass,   device: Tablet},
    {widget: Panel,      layout: Block,  system: Glass,   device: Phone},
    {widget: Panel,      layout: Block,  system: iOS,     device: Tablet},
    # ... 5,636 more combinations
    {widget: EmptyState, layout: Paint,  system: Office,  device: Desktop},
  ]
  
  for param in test_matrix:
    it "renders {param.widget} with {param.layout} layout on {param.device} ({param.system})":
      renderer = create_renderer(param.system, param.device)
      widget = create_widget(param.widget)
      layout_engine = get_layout_engine(param.layout)
      
      result = renderer.render(widget, layout_engine)
      
      expect(result.rendered).to_equal(true)
      expect(result.pixel_buffer.len).to_be_greater_than(0)
```

---

## Implementation Plan

### Phase 1: Test Generator (Week 1)

**Goal:** Automatic test case generation from matrix dimensions

**Deliverables:**
1. `test/03_system/check/gui_widget_matrix_generator.spl` — Generate 5,640 test cases
2. `test/03_system/check/gui_widget_parametrized_rendering_spec.spl` — Parametrized tests
3. `test/03_system/check/gui_widget_layout_matrix_spec.spl` — Layout algorithm tests
4. `test/03_system/check/gui_widget_design_system_spec.spl` — Design system tests

**Test Count:** 5,640 core tests

### Phase 2: Device Responsive Tests (Week 2)

**Goal:** Test all device breakpoints and orientations

**Deliverables:**
1. `test/03_system/check/gui_widget_responsive_phone_spec.spl` — Phone × Portrait/Landscape
2. `test/03_system/check/gui_widget_responsive_tablet_spec.spl` — Tablet × Portrait/Landscape
3. `test/03_system/check/gui_widget_responsive_desktop_spec.spl` — Desktop viewports

**Test Count:** 11,280 tests (with orientations)

### Phase 3: Viewport Sensitivity Tests (Week 3)

**Goal:** Test edge cases at breakpoint boundaries

**Deliverables:**
1. `test/03_system/check/gui_widget_breakpoint_edge_cases_spec.spl`
   - 599px → 600px transition (Phone/Tablet)
   - 767px → 768px transition (Tablet/Desktop)
   - 1023px → 1024px transition (Desktop)

**Test Count:** ~2,000 edge case tests

### Phase 4: Interaction & Accessibility (Week 4)

**Goal:** Test event handling and ARIA attributes per widget/device

**Deliverables:**
1. `test/03_system/check/gui_widget_interaction_matrix_spec.spl` — Click, keyboard, pointer
2. `test/03_system/check/gui_widget_accessibility_matrix_spec.spl` — ARIA, labels, roles

**Test Count:** 7,000+ tests

---

## Quick Reference: Test Case Count

| Dimension | Count | Notes |
|-----------|-------|-------|
| Widgets | 47 | All types from widget_kind.spl |
| Layouts | 8 | Block, Inline, Float, Table, Box, Flex, Grid, Paint |
| Design Systems | 5 | Glass, iOS, TUI, Browser, Office |
| Device Classes | 3 | Phone, Tablet, Desktop |
| **Core Matrix** | **5,640** | 47 × 8 × 5 × 3 |
| Orientations | 2 | Portrait, Landscape (mobile only) |
| **With Orientations** | **11,280** | 5,640 × 2 |
| Viewport Sizes | 3-4 | Per device class |
| **With Viewports** | **16,920-22,560** | Full coverage |
| Breakpoint Edges | ~2,000 | Transition testing |
| Interactions | ~7,000 | Click, keyboard, pointer |
| Accessibility | ~4,000 | ARIA, labels, roles |
| **GRAND TOTAL** | **~40,000-50,000** | Complete coverage |

---

## Test File Organization

```
test/03_system/check/
├── gui_widget_parametrized_rendering_spec.spl      (5,640 tests - Core)
├── gui_widget_responsive_phone_spec.spl              (3,760 tests - Phone + orientations)
├── gui_widget_responsive_tablet_spec.spl             (3,760 tests - Tablet + orientations)
├── gui_widget_responsive_desktop_spec.spl            (1,880 tests - Desktop)
├── gui_widget_breakpoint_edge_cases_spec.spl         (2,000 tests - Edges)
├── gui_widget_interaction_matrix_spec.spl            (7,000+ tests - Events)
├── gui_widget_accessibility_matrix_spec.spl          (4,000+ tests - A11y)
├── gui_widget_design_system_glass_spec.spl           (1,128 tests - Glass system)
├── gui_widget_design_system_ios_spec.spl             (1,128 tests - iOS system)
├── gui_widget_design_system_tui_spec.spl             (1,128 tests - TUI system)
├── gui_widget_design_system_browser_spec.spl         (1,128 tests - Browser system)
└── gui_widget_design_system_office_spec.spl          (1,128 tests - Office system)
```

---

## Parametrized Test Template

```spl
# GUI Widget Parametrized Test Template

use std.spec
use std.common.ui.widget_kind.{WidgetKind}
use std.common.ui.form_factor.{FormFactorProfile, DeviceClass}
use std.common.ui.style.{DesignSystem}
use std.nogc_sync_mut.engine.render.pipeline.{SoftwareRenderer}

describe "GUI Widget Parametrized Rendering (47 × 8 × 5 × 3 = 5,640 tests)":
  
  # Test matrix: all combinations of widgets, layouts, design systems, devices
  val widgets = [
    WidgetKind.Panel, WidgetKind.Text, WidgetKind.Button, WidgetKind.Input,
    # ... all 47 widgets
  ]
  
  val layouts = ["block", "inline", "float", "table", "box", "flex", "grid", "paint"]
  val systems = ["glass", "ios", "tui", "browser", "office"]
  val devices = [DeviceClass.Phone, DeviceClass.Tablet, DeviceClass.Desktop]
  
  for widget in widgets:
    for layout in layouts:
      for system in systems:
        for device in devices:
          val test_name = "{widget} × {layout} × {system} × {device}"
          
          it "renders {test_name}":
            val renderer = SoftwareRenderer.create(1024, 768)
            val widget_inst = WidgetKind.create(widget)
            
            val result = renderer.render_widget(
              widget: widget_inst,
              layout: layout,
              design_system: system,
              device: device
            )
            
            expect(result.success).to_equal(true)
            expect(result.pixels.len).to_be_greater_than(0)
```

---

## Success Criteria

✅ **Phase 1 Complete:** All 5,640 core parametrized tests pass  
✅ **Phase 2 Complete:** All 11,280 responsive tests pass (with orientations)  
✅ **Phase 3 Complete:** All 2,000 breakpoint edge cases pass  
✅ **Phase 4 Complete:** All 7,000+ interaction/accessibility tests pass  

**Coverage Target:** 40,000-50,000 total GUI rendering tests (vs. current 24 functional tests)

---

## Running Tests

```bash
# Core parametrized matrix (5,640 tests)
bin/simple test test/03_system/check/gui_widget_parametrized_rendering_spec.spl

# Responsive tests
bin/simple test test/03_system/check/gui_widget_responsive_*.spl

# All GUI tests (~45,000 tests)
bin/simple test test/03_system/check/gui_widget_*.spl

# Single design system
bin/simple test test/03_system/check/gui_widget_design_system_glass_spec.spl

# By device class
bin/simple test test/03_system/check/gui_widget_responsive_phone_spec.spl
```

---

## Benefits

| Benefit | Impact |
|---------|--------|
| **Comprehensive Coverage** | Every widget tested on every layout + device |
| **Regression Detection** | Layout bugs caught across 5,640+ combinations |
| **Design System Consistency** | All 5 systems validated for all 47 widgets |
| **Responsive Assurance** | Phone/Tablet/Desktop parity verified |
| **Accessibility Built-in** | ARIA + interactive patterns in matrix |
| **Performance Baseline** | Render time per widget/layout combination |

---

**Next Steps:**
1. Implement test generator (Phase 1)
2. Create parametrized rendering engine
3. Execute 5,640 core tests
4. Expand to 40,000+ with orientations and edge cases
