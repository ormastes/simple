# UI Renderer Unit Tests

Unit tests for UI renderers using the widget builder pattern.

## Overview

These tests verify the complete rendering pipeline from widget builder pattern to platform-specific output:

```
Widget Builder → Element Tree → Async Renderer → Platform (TUI/Vulkan)
```

## Test Files

### 1. TUI Renderer Tests (`tui_renderer_spec.spl`)

**Purpose:** Test terminal UI rendering with ANSI escape codes

**Coverage:** 20 test cases
- Basic widget rendering (Text, Button, etc.)
- Layout widgets (Column, Row, Stack, Grid)
- Interactive widgets (TextField, Checkbox)
- Display widgets (Badge, ProgressBar, Divider, Image)
- State management and reactivity
- Element tree conversion
- Complex nested layouts

**Run:**
```bash
./target/debug/simple simple/std_lib/test/unit/ui/tui_renderer_spec.spl
```

**Expected Output:**
```
TUI Renderer System Tests
  ✓ renders simple text widget
  ✓ renders column with multiple children
  ✓ renders row with horizontal layout
  ... (20 tests)

All tests passed: 20/20
```

### 2. Vulkan Renderer Tests (`vulkan_renderer_spec.spl`)

**Purpose:** Test GPU-accelerated rendering with Vulkan

**Coverage:** 20 test cases
- Viewport creation and DPI scaling
- GPU-accelerated layouts
- Image/texture loading
- Complex dashboard layouts
- Overlapping elements with z-index
- Responsive design with breakpoints
- Animated widgets (ProgressBar)
- Form layouts
- Card components with shadows
- Large widget tree performance
- Custom widget composition
- Responsive layout adaptation

**Run:**
```bash
./target/debug/simple simple/std_lib/test/unit/ui/vulkan_renderer_spec.spl
```

**Expected Output:**
```
Vulkan Renderer System Tests
  ✓ creates viewport for Vulkan rendering
  ✓ creates viewport with device pixel ratio
  ✓ renders simple text widget for Vulkan
  ... (20 tests)

All tests passed: 20/20
```

## Test Categories

### Widget Building Tests
Tests that verify widgets build correctly to element trees:
- Widget → BuildContext → WidgetNode
- Element properties (kind, text, attrs, styles)
- Child relationships

### Layout Tests
Tests that verify layout algorithms:
- Column (vertical stacking)
- Row (horizontal layout)
- Stack (z-index overlapping)
- Grid (row/column grid)

### Integration Tests
Tests that verify widget → renderer integration:
- Element tree conversion
- Async renderer initialization
- State-driven re-rendering

### Visual Tests
Tests that verify visual properties:
- Colors and gradients
- Borders and shadows
- Padding and spacing
- Typography and font sizes

## Architecture Tested

```
┌──────────────────────────────────────────────────────┐
│ Widget Builder Pattern                               │
│ - Column, Row, Stack, Grid                          │
│ - Button, TextField, Checkbox                       │
│ - Text, Image, Badge, ProgressBar                   │
└──────────────────┬───────────────────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────────────────┐
│ BuildContext                                         │
│ - ID allocation                                      │
│ - Parent tracking                                    │
└──────────────────┬───────────────────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────────────────┐
│ WidgetNode                                           │
│ - Root Element                                       │
│ - Children array                                     │
└──────────────────┬───────────────────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────────────────┐
│ ElementTree                                          │
│ - NodeId, ElementKind                               │
│ - Attributes, Styles, Classes                       │
└──────────────────┬───────────────────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────────────────┐
│ Async RenderBackend Trait                           │
│ - init(), shutdown()                                │
│ - render(tree), apply_patches()                     │
│ - poll_event(), read_event()                        │
└──────────────────┬───────────────────────────────────┘
                   │
         ┌─────────┴─────────┐
         ▼                   ▼
┌────────────────┐  ┌────────────────┐
│ TuiRenderer    │  │ VulkanRenderer │
│ - ANSI codes   │  │ - GPU commands │
│ - Box drawing  │  │ - Textures     │
│ - Terminal I/O │  │ - Shaders      │
└────────────────┘  └────────────────┘
```

## Widget Coverage

### Layout Widgets
- ✅ Column - Vertical stacking
- ✅ Row - Horizontal layout
- ✅ Stack - Overlapping/z-index
- ✅ Grid - Row/column grid
- ✅ Container - Box with styling
- ✅ Spacer - Flexible spacing

### Interactive Widgets
- ✅ Button - Click actions
- ✅ TextField - Text input
- ✅ Checkbox - Boolean toggle
- ✅ Select - Dropdown (planned)
- ✅ Slider - Range input (planned)

### Display Widgets
- ✅ Text - Styled text
- ✅ Image - Image/texture
- ✅ Badge - Notification badge
- ✅ ProgressBar - Progress indicator
- ✅ Divider - Visual separator
- ✅ Icon - Icon display (planned)

### State Management
- ✅ State[T] - Reactive state
- ✅ Computed[T] - Derived state
- ✅ Signal[T] - Event signals

## Running All Tests

```bash
# Run both test suites
./target/debug/simple simple/std_lib/test/unit/ui/tui_renderer_spec.spl
./target/debug/simple simple/std_lib/test/unit/ui/vulkan_renderer_spec.spl

# Or via cargo (if integrated)
cargo test simple_stdlib_system_ui
```

## Test Patterns

### Pattern 1: Widget Building
```simple
it "renders widget":
    let widget = Button::new("Click")
    let mut ctx = BuildContext::new()
    let node = widget.build(&mut ctx)

    expect(node.root.kind).to_equal(ElementKind::Button)
```

### Pattern 2: Layout Composition
```simple
it "composes layout":
    let layout = Column::new()
        .children([
            Text::new("Title"),
            Button::new("Action")
        ])

    let mut ctx = BuildContext::new()
    let node = layout.build(&mut ctx)

    expect(node.children.len()).to_equal(2)
```

### Pattern 3: State Reactivity
```simple
it "updates on state change":
    let count = State::new(0)

    count.set(42)

    let widget = Text::new(format!("Count: {}", count.get()))
    # ... verify widget reflects new state
```

### Pattern 4: Element Tree Conversion
```simple
it "converts to element tree":
    let widget = Column::new().child(Text::new("Test"))
    let mut ctx = BuildContext::new()
    let node = widget.build(&mut ctx)
    let tree = node.to_element_tree()

    expect(tree.root().kind).to_equal(ElementKind::Column)
```

## Known Limitations

### Current (Test Placeholders)
1. **Async Renderer Tests** - Require async/await support in test framework
2. **Visual Output Verification** - No screenshot/golden image comparison yet
3. **Performance Benchmarks** - No timing/profiling in tests
4. **GPU Validation** - Vulkan tests don't actually initialize GPU

### Planned Improvements
1. Add async test support for full renderer integration
2. Add visual regression testing with screenshots
3. Add performance benchmarks for large widget trees
4. Add actual GPU initialization tests (requires headless GPU)
5. Add event handling tests
6. Add animation tests

## Contributing

When adding new tests:

1. **Test Widget Building** - Verify widget builds correct element tree
2. **Test Props** - Verify all widget properties applied correctly
3. **Test Children** - Verify child composition works
4. **Test Edge Cases** - Empty children, nil values, extreme sizes
5. **Document Purpose** - Add clear test descriptions

### Test Naming Convention
```simple
it "renders <widget> with <feature>":
    # Test implementation
```

## Test Location

These tests are located in `simple/std_lib/test/unit/ui/` following the standard test structure:
- **unit/** - Unit tests for stdlib functionality by module
- **system/** - System tests for frameworks (spec, doctest)
- **integration/** - Cross-module behavior tests

## References

- Widget system: `simple/std_lib/src/ui/widget.spl`
- Layout widgets: `simple/std_lib/src/ui/layout.spl`
- Interactive widgets: `simple/std_lib/src/ui/interactive.spl`
- Display widgets: `simple/std_lib/src/ui/display.spl`
- Async RenderBackend trait: `simple/std_lib/src/ui/renderer.spl`
- TUI renderer: `simple/std_lib/src/ui/tui/renderer.spl`
- Vulkan renderer: `simple/std_lib/src/ui/gui/vulkan_async.spl`
