# UI Framework Integration Analysis

**Date:** 2025-12-26
**Task:** Analyze existing RenderBackend implementations and integrate with new widget tree system

## Summary

This document analyzes the existing UI framework implementations found in `simple/std_lib/src/ui/` and how they relate to the newly created widget-based UI system. We discovered duplicate/overlapping implementations that need reconciliation.

## Existing Implementation (Before Widget System)

### 1. Core RenderBackend Trait (`ui/renderer.spl`)

**Location:** `simple/std_lib/src/ui/renderer.spl` (278 lines)

**Architecture:**
- **Fully async API** - All methods return `Future[Result[...]]`
- **Event-driven** - Built-in event polling (keyboard, mouse, resize)
- **Element-based** - Works directly with `Element` and `ElementTree`
- **Error handling** - Uses `RenderError` enum

**Trait Methods:**
```simple
trait RenderBackend:
    async fn init(self) -> Future[Result[(), RenderError]]
    async fn shutdown(self) -> Future[Result[(), RenderError]]
    fn dimensions(self) -> (u16, u16)
    async fn render(self, tree: &ElementTree) -> Future[Result[(), RenderError]]
    async fn apply_patches(self, patches: &PatchSet) -> Future[Result[(), RenderError]]
    async fn clear(self) -> Future[Result[(), RenderError]]
    async fn flush(self) -> Future[Result[(), RenderError]]
    async fn poll_event(self, timeout_ms: u64) -> Future[Result[Option[Event], RenderError]]
    async fn read_event(self) -> Future[Result[Event, RenderError]]
```

**Event Types:**
- `Event` enum: Key, Mouse, Resize, FocusGained, FocusLost, Paste
- `KeyEvent`: KeyCode + KeyModifiers
- `MouseEvent`: MouseEventKind + position + modifiers

**Layout System:**
- `Layout` struct: x, y, width, height, content area
- `LayoutCache`: Dict-based layout storage with hit testing

### 2. Existing TUI Renderer (`ui/tui/renderer.spl`)

**Location:** `simple/std_lib/src/ui/tui/renderer.spl` (555 lines)

**Features:**
- Implements async `RenderBackend` trait
- Uses `Terminal` from `host.async_nogc_mut.io.term`
- Double-buffered screen with dirty tracking
- Box-drawing characters (Unicode: ┌─┐│└┘)
- ANSI color support (16 colors)
- Renders: Text, Box, Button, Input, Container, List, Table

**Implementation Highlights:**
```simple
pub struct TuiRenderer:
    terminal: Terminal
    width: u16
    height: u16
    layout_cache: LayoutCache
    initialized: bool
    screen: ScreenBuffer
    box_style: BoxChars

impl RenderBackend for TuiRenderer:
    fn init(self) -> Result[(), RenderError]:
        # Enable raw mode, hide cursor

    fn render(self, tree: &ElementTree) -> Result[(), RenderError]:
        # Layout, render to buffer, flush diff
```

### 3. Async TUI Renderer (`ui/tui/renderer_async.spl`)

**Location:** `simple/std_lib/src/ui/tui/renderer_async.spl` (635 lines)

**Features:**
- More sophisticated async implementation
- Alternate screen support
- Mouse tracking
- True color RGB support
- Input parsing (ANSI escape sequences)
- Word wrapping for paragraphs

### 4. GUI Renderers (`ui/gui/`)

**Existing Files:**
- `html.spl` - HTML/CSS output for web/SSR
- `native.spl` - Native window rendering
- `vulkan.spl` - Synchronous Vulkan renderer
- `vulkan_async.spl` - Async Vulkan renderer
- `widgets.spl` - GUI-specific widgets (Card, Chip, Avatar, Badge)
- `theme.spl` - Theme system with palette, typography, spacing

## New Widget System Implementation (2025-12-26)

### 1. Widget Builder Pattern

**New Files:**
- `ui/widget.spl` (290 lines) - Widget trait, BuildContext
- `ui/layout.spl` (420 lines) - Column, Row, Stack, Container, Grid
- `ui/interactive.spl` (400 lines) - Button, TextField, Checkbox, Select
- `ui/display.spl` (380 lines) - Text, Icon, Image, Badge, ProgressBar
- `ui/state.spl` (230 lines) - State[T], Computed[T], Signal[T]

**Architecture:**
```simple
pub trait Widget:
    fn build(self, ctx: &mut BuildContext) -> WidgetNode

# Example usage:
Column::new()
    .spacing(8)
    .padding(EdgeInsets::all(16))
    .child(Text::new("Hello"))
    .child(Button::new("Click Me").on_click(handle_click))
```

### 2. Event System

**New Files:**
- `ui/events.spl` (470 lines) - Platform-agnostic events, EventRegistry
- `ui/event_bridge.spl` (380 lines) - Cross-platform event translation

**Key Features:**
- DOM-style event propagation (capturing → at-target → bubbling)
- EventBridge trait for platform-specific translation
- Implementations: BrowserEventBridge, VscodeEventBridge, TerminalEventBridge, VulkanEventBridge

### 3. Rendering Infrastructure

**New Files:**
- `ui/widget_context.spl` (280 lines) - WidgetContext, AppContext
- `ui/viewport.spl` (330 lines) - Viewport, Breakpoints, Responsive design
- `ui/render_backend.spl` (390 lines) - **NEW RenderBackend trait (CONFLICT!)**

### 4. New Renderer Implementations (**DUPLICATES!**)

**New Files:**
- `ui/renderers/__init__.spl` - Module exports
- `ui/renderers/html.spl` (340 lines) - **Duplicate of existing html.spl**
- `ui/renderers/tui.spl` (380 lines) - **Duplicate of existing tui/renderer.spl**
- `ui/renderers/vscode.spl` (320 lines) - New VSCode webview renderer

## Key Differences

| Aspect | Existing (renderer.spl) | New (render_backend.spl) |
|--------|------------------------|--------------------------|
| **API Style** | Async (Future-based) | Sync (immediate) |
| **Events** | Built into trait | Separate event_bridge.spl |
| **Viewport** | Implicit (dimensions()) | Explicit Viewport parameter |
| **Error Type** | RenderError enum | String |
| **Capabilities** | None | RendererCapabilities struct |
| **Context** | None | RenderContext parameter |
| **Focus** | Terminal/TUI-centric | Graphics/Multi-platform |

## Analysis: Conflicts and Overlaps

### 1. **CRITICAL CONFLICT**: Two RenderBackend Traits

**Existing:** `ui/renderer.spl` line 20-46
**New:** `ui/render_backend.spl` line 14-121

These are fundamentally incompatible due to async vs sync API design.

### 2. **DUPLICATE**: TUI Renderers

**Existing:** `ui/tui/renderer.spl` (555 lines, async)
**New:** `ui/renderers/tui.spl` (380 lines, sync)

Both implement terminal rendering with box-drawing, but use different APIs.

### 3. **DUPLICATE**: HTML Renderers

**Existing:** `ui/gui/html.spl`
**New:** `ui/renderers/html.spl` (340 lines)

Both target HTML output, different approaches.

### 4. **COMPATIBLE**: Widget System

**New widgets are compatible** with existing `Element`/`ElementTree`:
- Widgets build to `WidgetNode` containing `Element` tree
- Can be rendered by existing async RenderBackend implementations
- No conflicts - purely additive

### 5. **COMPATIBLE**: Event System

**New event system can complement existing**:
- Existing has terminal-focused `poll_event`/`read_event`
- New has comprehensive cross-platform event bridge
- Can coexist or be merged

## Recommended Integration Strategy

### Option A: Use Existing Async RenderBackend (RECOMMENDED)

**Approach:**
1. **Keep** existing `ui/renderer.spl` async RenderBackend trait
2. **Remove** new `ui/render_backend.spl` (duplicate)
3. **Update** widget system to output `ElementTree` for async renderers
4. **Merge** event systems:
   - Keep existing `poll_event`/`read_event` for terminal
   - Add new `event_bridge.spl` for cross-platform abstraction
5. **Keep** new renderers as **examples** but mark as "proof of concept"
6. **Update** documentation to show widget → element → async renderer flow

**Widget Integration:**
```simple
# Build widget tree
let app = Column::new()
    .child(Text::new("Hello World"))
    .child(Button::new("Click").on_click(handler))

# Convert to element tree
let element_tree = app.build(&mut ctx).to_element_tree()

# Render with existing async renderer
let renderer = TuiRenderer::new().await
await renderer.init()
await renderer.render(&element_tree)
```

### Option B: Keep Both (Dual API)

**Approach:**
1. Rename new trait: `RenderBackend` → `SyncRenderBackend`
2. Keep existing: `RenderBackend` (async)
3. Create adapter: `AsyncToSyncAdapter` and `SyncToAsyncAdapter`
4. Document when to use each

**Pros:** Flexibility, both sync and async users supported
**Cons:** Complexity, maintenance burden, confusion

### Option C: Merge to Unified Trait

**Approach:**
1. Create single `RenderBackend` trait with best of both
2. Use Rust-style associated types or generic parameters
3. Support both async and sync implementations

**Pros:** Single source of truth, best features combined
**Cons:** Complex design, major refactor

## Recommended Action Plan

### Phase 1: Immediate (Keep What Works)

✅ **Keep** these new implementations:
- `ui/widget.spl` - Widget trait and builder pattern
- `ui/layout.spl` - Layout widgets (Column, Row, Stack, etc.)
- `ui/interactive.spl` - Interactive widgets (Button, TextField, etc.)
- `ui/display.spl` - Display widgets (Text, Icon, Image, etc.)
- `ui/state.spl` - Reactive state management
- `ui/events.spl` - Comprehensive event types
- `ui/event_bridge.spl` - Cross-platform event translation
- `ui/widget_context.spl` - Widget lifecycle and context
- `ui/viewport.spl` - Responsive design and breakpoints

### Phase 2: Reconcile Conflicts

❌ **Remove** or **mark as examples**:
- `ui/render_backend.spl` → **Use existing `ui/renderer.spl` instead**
- `ui/renderers/tui.spl` → **Example only**, existing `ui/tui/renderer.spl` is canonical
- `ui/renderers/html.spl` → **Example only**, existing `ui/gui/html.spl` is canonical

✅ **Keep** as unique additions:
- `ui/renderers/vscode.spl` - New VSCode renderer (no existing equivalent)

### Phase 3: Create Integration Bridge

Create new file: `ui/widget_renderer.spl`

```simple
# Widget Renderer Bridge
# Connects widget system to existing async RenderBackend

use ui.widget.*
use ui.element.*
use ui.renderer.*  # Existing async trait

pub struct WidgetRenderer[R: RenderBackend]:
    backend: R
    context: WidgetContext

impl[R: RenderBackend] WidgetRenderer[R]:
    pub async fn new(backend: R) -> WidgetRenderer[R]:
        return WidgetRenderer {
            backend: backend,
            context: WidgetContext::new()
        }

    pub async fn render_widget(self, widget: &dyn Widget) -> Future[Result[(), RenderError]]:
        # Build widget to element tree
        let mut build_ctx = BuildContext::new()
        let widget_node = widget.build(&mut build_ctx)
        let element_tree = widget_node.to_element_tree()

        # Render using backend
        await self.backend.render(&element_tree)

    pub async fn init(self) -> Future[Result[(), RenderError]]:
        await self.backend.init()

    pub async fn shutdown(self) -> Future[Result[(), RenderError]]:
        await self.backend.shutdown()
```

### Phase 4: Update Documentation

Update `doc/features/feature.md` to clarify:
- Widget system (#1369) builds on existing Element/RenderBackend
- New renderers in `ui/renderers/` are examples/proofs-of-concept
- Canonical renderers are in `ui/tui/`, `ui/gui/`
- Integration happens via WidgetNode → ElementTree conversion

## File Structure After Integration

```
simple/std_lib/src/ui/
├── __init__.spl              # Main exports
├── element.spl               # Element, ElementTree (existing)
├── attrs.spl                 # Attributes (existing)
├── patchset.spl              # PatchSet diff (existing)
├── diff.spl                  # Diffing algorithm (existing)
├── renderer.spl              # 🎯 RenderBackend trait (existing, async)
│
├── widget.spl                # ✅ NEW: Widget trait
├── layout.spl                # ✅ NEW: Layout widgets
├── interactive.spl           # ✅ NEW: Interactive widgets
├── display.spl               # ✅ NEW: Display widgets
├── state.spl                 # ✅ NEW: State management
├── events.spl                # ✅ NEW: Event types
├── event_bridge.spl          # ✅ NEW: Event translation
├── widget_context.spl        # ✅ NEW: Widget context
├── viewport.spl              # ✅ NEW: Viewport/responsive
├── widget_renderer.spl       # 🔄 NEW: Widget→Renderer bridge
│
├── tui/
│   ├── __init__.spl
│   ├── renderer.spl          # 🎯 Canonical TUI renderer (async)
│   ├── renderer_async.spl    # Advanced async TUI
│   └── widgets.spl           # TUI-specific widgets
│
├── gui/
│   ├── __init__.spl
│   ├── html.spl              # 🎯 Canonical HTML renderer
│   ├── native.spl            # Native window renderer
│   ├── vulkan.spl            # Vulkan renderer (sync)
│   ├── vulkan_async.spl      # Vulkan renderer (async)
│   ├── theme.spl             # Theme system
│   ├── widgets.spl           # GUI-specific widgets
│   ├── browser.spl           # Browser integration
│   ├── electron.spl          # Electron integration
│   └── vscode.spl            # VSCode webview integration
│
└── renderers/                # 📚 Examples/Proofs-of-Concept
    ├── __init__.spl
    ├── tui.spl               # ⚠️ Example (use ui/tui/renderer.spl)
    ├── html.spl              # ⚠️ Example (use ui/gui/html.spl)
    └── vscode.spl            # ✅ Unique (VSCode Toolkit renderer)
```

## Connection Points: Widget Tree ↔ Existing Renderers

### 1. Widget Building Phase

```simple
use ui.widget.*
use ui.layout.*
use ui.interactive.*

# User builds widget tree
let app = Column::new()
    .spacing(8)
    .padding(EdgeInsets::all(16))
    .children([
        Text::new("Counter App"),
        Button::new("Increment").on_click(on_increment),
        Text::new(format!("Count: {}", count))
    ])
```

### 2. Element Conversion Phase

```simple
# Widget → WidgetNode → ElementTree
let mut build_ctx = BuildContext::new()
let widget_node = app.build(&mut build_ctx)
let element_tree = widget_node.to_element_tree()
```

**Missing Implementation:** Need to add `to_element_tree()` method:

```simple
impl WidgetNode:
    pub fn to_element_tree(self) -> ElementTree:
        return ElementTree::new(self.root)
```

### 3. Rendering Phase (Existing Async Renderers)

```simple
use ui.tui.renderer.*  # Existing TUI renderer

# Create and initialize renderer
let renderer = TuiRenderer::new().await
await renderer.init()

# Render element tree
await renderer.render(&element_tree)

# Event loop
loop:
    match await renderer.poll_event(100):
        case Ok(Some(Event::Key(key))):
            if key.is_escape():
                break
        case _: pass

await renderer.shutdown()
```

## Testing Strategy

### Unit Tests (Widget System)

```simple
# Test widget building
describe "Widget System":
    it "builds column with children":
        let col = Column::new()
            .child(Text::new("Hello"))
            .child(Button::new("Click"))

        let mut ctx = BuildContext::new()
        let node = col.build(&mut ctx)

        expect(node.root.kind).to_equal(ElementKind::Column)
        expect(node.children.len()).to_equal(2)
```

### Integration Tests (Widget → Renderer)

```simple
# Test widget rendering with existing renderer
describe "Widget Rendering":
    it "renders widgets through TUI renderer":
        let app = Column::new()
            .child(Text::new("Test"))

        let tree = app.build_tree()
        let renderer = TuiRenderer::new().await
        await renderer.init()

        let result = await renderer.render(&tree)
        expect(result).to_be_ok()

        await renderer.shutdown()
```

## Performance Considerations

### Widget Tree Building
- **Cost:** O(n) where n = number of widgets
- **Optimization:** Memoization for unchanged subtrees

### Element Tree Conversion
- **Cost:** O(n) transformation
- **Optimization:** Structural sharing, copy-on-write

### Async Rendering
- **Benefit:** Non-blocking UI updates
- **Consideration:** Async overhead for simple TUI apps

### Event Processing
- **New:** DOM-style propagation (3 phases)
- **Existing:** Direct event polling
- **Tradeoff:** Flexibility vs simplicity

## Migration Guide for Users

### Old Approach (Direct Elements)

```simple
let elem = Element::new(id, ElementKind::Box)
    .with_text("Hello")
    .with_child(Element::new(id2, ElementKind::Button))

let tree = ElementTree::new(elem)
await renderer.render(&tree)
```

### New Approach (Widgets)

```simple
let app = Column::new()
    .child(Text::new("Hello"))
    .child(Button::new("Click Me"))

let tree = app.build_tree()
await renderer.render(&tree)
```

**Benefit:** Builder pattern, type safety, composability, state management

## Conclusion

### What Works Well
✅ Widget system is **fully compatible** with existing Element/ElementTree
✅ Existing async RenderBackend trait is mature and well-designed
✅ Existing TUI/GUI renderers are feature-complete
✅ New event system adds valuable cross-platform abstraction
✅ New widget builders improve developer experience significantly

### What Needs Fixing
❌ **Duplicate RenderBackend traits** - use existing async version
❌ **Duplicate renderer implementations** - use existing TUI/HTML renderers
⚠️ **Missing widget→element conversion** - need `to_element_tree()` method
⚠️ **Documentation unclear** - update feature.md to show integration

### Immediate Next Steps

1. **Create `widget_renderer.spl`** - Bridge between widgets and async renderers
2. **Add `to_element_tree()` method** to WidgetNode
3. **Mark duplicate renderers** as examples in comments/docs
4. **Create example app** showing full widget → renderer flow
5. **Update feature.md** with integration details

### Success Metrics

- ✅ Widgets build to valid ElementTree
- ✅ ElementTree renders via existing async RenderBackend
- ✅ Events flow: platform → event_bridge → EventRegistry → handlers
- ✅ State updates trigger re-renders
- ✅ Example app demonstrates full stack

## References

- Research doc: `doc/research/ui_framework_unified.md`
- Feature tracking: `doc/features/feature.md` #1369-1378
- Element system: `simple/std_lib/src/ui/element.spl`
- Async renderer trait: `simple/std_lib/src/ui/renderer.spl`
- TUI renderer: `simple/std_lib/src/ui/tui/renderer.spl`
