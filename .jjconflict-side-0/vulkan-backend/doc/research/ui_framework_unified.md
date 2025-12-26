# Unified UI Framework Research

**Date:** 2025-12-26
**Status:** Research Document
**Related:** [feature.md](../features/feature.md) #1369-1378 (UI Frameworks), #1404-1420 (Electron), #1421-1440 (VSCode)

## Executive Summary

This document analyzes GUI description approaches and proposes a unified UI API that supports multiple render targets (Browser, Electron, VSCode, TUI) while maintaining consistency with Simple's existing `.sui` template system.

**Key Recommendations:**
1. **Hybrid Approach**: Keep `.sui` templates for declarative UI + add Builder Pattern API for programmatic UI
2. **Widget Abstraction**: Create `Widget` trait with platform-specific renderers
3. **VSCode Integration**: Use VSCode Toolkit web components in webviews
4. **Electron Strategy**: Share Browser renderer for web-based UI, native APIs for system integration

---

## 1. Current Simple UI Architecture

### 1.1 SUI Template System

Simple uses `.sui` template files with a unique multi-block structure:

```
┌─────────────────────────────────────────┐
│  {@ page/component/layout @}            │  ← Type declaration
├─────────────────────────────────────────┤
│  {$ let count: i32 = 0 $}               │  ← Shared state
├─────────────────────────────────────────┤
│  {- server -}                           │  ← Server block (SSR)
│    fn load_data(): db.query(...)        │
├─────────────────────────────────────────┤
│  {+ client +}                           │  ← Client block (WASM)
│    on_click("#btn", fn(): count += 1)   │
├─────────────────────────────────────────┤
│  {@ render @}                           │  ← Template (HTML)
│  <div>{{ count }}</div>                 │
└─────────────────────────────────────────┘
```

### 1.2 AST Structure (src/ui/src/parser/ast.rs)

```rust
pub struct SuiTemplate {
    pub kind: TemplateKind,       // Page | Component | Layout
    pub name: String,
    pub declarations: Vec<StateDecl>,
    pub server_block: Option<ServerBlock>,
    pub client_block: Option<ClientBlock>,
    pub content: Vec<TemplateNode>,
}

pub enum TemplateNode {
    Element(Element),       // <tag attr="value">children</tag>
    Text(TextNode),         // Plain text
    Output(OutputNode),     // {{ expr }}
    RawOutput(OutputNode),  // {! expr !}
    Control(ControlNode),   // {% if/for/let %}
    Embed(EmbedNode),       // {@ embed Component @}
    Slot(SlotNode),         // {@ slot name @}
    Fill(FillNode),         // {@ fill name @}
}
```

### 1.3 RenderBackend Trait (src/ui/src/render/backend.rs)

```rust
pub trait RenderBackend {
    type Node;
    type Context;
    type Error;

    fn create_element(&mut self, ctx: &mut Self::Context, tag: &str) -> Result<Self::Node, Self::Error>;
    fn create_text(&mut self, ctx: &mut Self::Context, text: &str) -> Result<Self::Node, Self::Error>;
    fn set_attr(&mut self, node: &mut Self::Node, name: &str, value: &str) -> Result<(), Self::Error>;
    fn append_child(&mut self, parent: &mut Self::Node, child: Self::Node) -> Result<(), Self::Error>;
    fn apply_patch(&mut self, ctx: &mut Self::Context, patch: &PatchOp) -> Result<(), Self::Error>;
}
```

### 1.4 Compilation Pipeline

```
.sui file → Parser → SuiTemplate AST
                          ↓
              ┌───────────┴───────────┐
              ↓                       ↓
         InitIR              TemplateIR + RenderIR
              ↓                       ↓
    Server (x64 native)      Client (wasm32)
              ↓                       ↓
         SSR HTML ──────────────→ Hydration
```

---

## 2. GUI Description Approaches Comparison

### 2.1 Approach Matrix

| Approach | Examples | Description | Pros | Cons |
|----------|----------|-------------|------|------|
| **Declarative Templates** | Vue SFC, Svelte, Simple SUI | HTML-like markup with bindings | Designer-friendly, SSR, familiar | Limited programmatic control |
| **JSX/TSX** | React, Solid, Preact | JavaScript expressions in markup | Composable, IDE support | Requires transpilation |
| **Immediate Mode** | Dear ImGui, egui, Raylib | Redraw every frame | Real-time, simple state | No SSR, inefficient for static |
| **Retained Mode** | Qt, GTK, WxWidgets, Flutter | Persistent widget tree | Full control, native look | Complex state management |
| **Builder Pattern** | SwiftUI, Jetpack Compose, Slint | Fluent API, method chaining | Type-safe, declarative, composable | Learning curve |
| **DSL Macro** | Yew html!, Dioxus rsx!, Leptos view! | Compile-time macros | Zero runtime overhead | Macro complexity, debugging |
| **Functional Reactive** | Elm, Halogen, Reflex-FRP | Pure functions + signals | Predictable, testable | Steep learning curve |
| **XAML/XML** | WPF, UWP, Avalonia | External markup files | Separation of concerns | Verbose, tooling dependent |

### 2.2 Fit Analysis for Simple

| Approach | Browser | Electron | VSCode | TUI | Recommendation |
|----------|---------|----------|--------|-----|----------------|
| **Declarative Templates** | ✅ Current | ✅ | ⚠️ Limited | ⚠️ | Keep for pages |
| **Builder Pattern** | ✅ | ✅ | ✅ | ✅ | **Add for widgets** |
| **Immediate Mode** | ❌ | ❌ | ❌ | ⚠️ Games only | Not recommended |
| **DSL Macro** | ⚠️ | ⚠️ | ⚠️ | ⚠️ | Future consideration |

**Recommendation:** Hybrid approach using:
1. `.sui` templates for page/layout structure (current)
2. Builder Pattern for reusable widgets (new)
3. Platform-specific renderers via `RenderBackend` trait

---

## 3. Builder Pattern API Design

### 3.1 Core Widget Types

```simple
# Base widget trait
trait Widget:
    fn build(self, ctx: BuildContext) -> WidgetNode

# Layout widgets
class Column(Widget):
    children: List[Widget]
    spacing: i32 = 0
    align: Align = Align.Start

    fn spacing(mut self, px: i32) -> Self:
        self.spacing = px
        return self

    fn child(mut self, widget: Widget) -> Self:
        self.children.append(widget)
        return self

class Row(Widget):
    children: List[Widget]
    spacing: i32 = 0
    justify: Justify = Justify.Start

class Stack(Widget):
    children: List[Widget]
    alignment: Alignment = Alignment.TopLeft

# Container widgets
class Container(Widget):
    child: Option[Widget]
    padding: EdgeInsets = EdgeInsets.zero()
    margin: EdgeInsets = EdgeInsets.zero()
    decoration: Option[BoxDecoration]

class Card(Widget):
    child: Option[Widget]
    elevation: i32 = 1

class ScrollView(Widget):
    child: Widget
    direction: ScrollDirection = ScrollDirection.Vertical
```

### 3.2 Interactive Widgets

```simple
class Button(Widget):
    label: String
    icon: Option[Icon]
    on_click: Option[fn()]
    variant: ButtonVariant = ButtonVariant.Primary
    disabled: bool = false

    fn new(label: String) -> Self:
        Button { label: label, icon: None, on_click: None,
                 variant: ButtonVariant.Primary, disabled: false }

    fn on_click(mut self, handler: fn()) -> Self:
        self.on_click = Some(handler)
        return self

    fn icon(mut self, icon: Icon) -> Self:
        self.icon = Some(icon)
        return self

    fn disabled(mut self, value: bool) -> Self:
        self.disabled = value
        return self

class TextField(Widget):
    value: String
    placeholder: String = ""
    on_change: Option[fn(String)]
    on_submit: Option[fn(String)]
    multiline: bool = false

class Checkbox(Widget):
    checked: bool
    label: String
    on_change: Option[fn(bool)]

class Select(Widget):
    options: List[(String, String)]  # (value, label)
    selected: Option[String]
    on_change: Option[fn(String)]

class Slider(Widget):
    value: f64
    min: f64 = 0.0
    max: f64 = 100.0
    on_change: Option[fn(f64)]
```

### 3.3 Display Widgets

```simple
class Text(Widget):
    content: String
    style: TextStyle = TextStyle.body()

    fn new(content: String) -> Self:
        Text { content: content, style: TextStyle.body() }

    fn style(mut self, style: TextStyle) -> Self:
        self.style = style
        return self

class Icon(Widget):
    name: String
    size: i32 = 24
    color: Option[Color]

class Image(Widget):
    src: String
    width: Option[i32]
    height: Option[i32]
    fit: ImageFit = ImageFit.Contain

class ProgressBar(Widget):
    value: f64  # 0.0 to 1.0
    indeterminate: bool = false

class Badge(Widget):
    content: String
    variant: BadgeVariant = BadgeVariant.Default
```

### 3.4 Usage Example

```simple
import ui.{Column, Row, Button, Text, TextField, Card}

fn build_login_form(state: LoginState) -> Widget:
    Card.new()
        .child(
            Column.new()
                .spacing(16)
                .child(Text.new("Login").style(TextStyle.h2()))
                .child(
                    TextField.new()
                        .placeholder("Email")
                        .value(state.email)
                        .on_change(fn(v): state.email = v)
                )
                .child(
                    TextField.new()
                        .placeholder("Password")
                        .value(state.password)
                        .on_change(fn(v): state.password = v)
                )
                .child(
                    Row.new()
                        .justify(Justify.End)
                        .spacing(8)
                        .child(Button.new("Cancel").variant(ButtonVariant.Secondary))
                        .child(Button.new("Login").on_click(handle_login))
                )
        )
```

---

## 4. Platform-Specific Rendering

### 4.1 Render Target Architecture

```
                    Widget (Builder API)
                           │
              ┌────────────┼────────────┐
              ▼            ▼            ▼
         HtmlRenderer  TuiRenderer  VscodeRenderer
              │            │            │
              ▼            ▼            ▼
         Browser DOM   Terminal    Webview HTML
         Electron      (crossterm) (vscode-toolkit)
```

### 4.2 HTML Renderer (Browser + Electron)

```simple
# simple/std_lib/src/ui/render/html.spl

class HtmlRenderer impl RenderBackend:
    doc: DomDocument

    fn render_button(self, btn: Button) -> HtmlElement:
        let el = self.doc.create_element("button")
        el.set_attribute("class", "btn btn-" + btn.variant.to_string())

        if btn.icon.is_some():
            let icon_el = self.doc.create_element("span")
            icon_el.set_attribute("class", "icon icon-" + btn.icon.unwrap().name)
            el.append_child(icon_el)

        let text_el = self.doc.create_text_node(btn.label)
        el.append_child(text_el)

        if btn.on_click.is_some():
            el.add_event_listener("click", btn.on_click.unwrap())

        if btn.disabled:
            el.set_attribute("disabled", "true")

        return el

    fn render_column(self, col: Column) -> HtmlElement:
        let el = self.doc.create_element("div")
        el.set_attribute("class", "flex flex-col")
        el.set_attribute("style", "gap: " + col.spacing.to_string() + "px")

        for child in col.children:
            el.append_child(self.render(child))

        return el
```

### 4.3 TUI Renderer (Terminal)

```simple
# simple/std_lib/src/ui/render/tui.spl

class TuiRenderer impl RenderBackend:
    buffer: TerminalBuffer

    fn render_button(self, btn: Button) -> TuiNode:
        let label = if btn.icon.is_some():
            btn.icon.unwrap().to_ascii() + " " + btn.label
        else:
            btn.label

        let style = if btn.disabled:
            Style.dim()
        else:
            Style.bold()

        return TuiNode.text("[ " + label + " ]", style)

    fn render_column(self, col: Column) -> TuiNode:
        let lines = []
        for i, child in col.children.enumerate():
            if i > 0 and col.spacing > 0:
                # Add spacing lines
                for _ in range(col.spacing / 8):
                    lines.append(TuiNode.empty_line())
            lines.append(self.render(child))

        return TuiNode.vertical_layout(lines)
```

### 4.4 VSCode Renderer (Webview)

```simple
# simple/std_lib/src/ui/render/vscode.spl

class VscodeRenderer impl RenderBackend:
    doc: DomDocument

    fn render_button(self, btn: Button) -> HtmlElement:
        # Use VSCode Toolkit components
        let el = self.doc.create_element("vscode-button")

        match btn.variant:
            ButtonVariant.Primary => el.set_attribute("appearance", "primary")
            ButtonVariant.Secondary => el.set_attribute("appearance", "secondary")
            ButtonVariant.Icon => el.set_attribute("appearance", "icon")

        if btn.icon.is_some():
            let icon_el = self.doc.create_element("span")
            icon_el.set_attribute("class", "codicon codicon-" + btn.icon.unwrap().name)
            icon_el.set_attribute("slot", "start")
            el.append_child(icon_el)

        let text = self.doc.create_text_node(btn.label)
        el.append_child(text)

        if btn.disabled:
            el.set_attribute("disabled", "")

        # VSCode webview message passing
        if btn.on_click.is_some():
            el.add_event_listener("click", fn():
                vscode.postMessage({ type: "button_click", id: btn.id })
            )

        return el

    fn render_text_field(self, field: TextField) -> HtmlElement:
        let el = self.doc.create_element("vscode-text-field")
        el.set_attribute("value", field.value)
        el.set_attribute("placeholder", field.placeholder)

        if field.multiline:
            # Use vscode-text-area for multiline
            el = self.doc.create_element("vscode-text-area")
            el.set_attribute("value", field.value)
            el.set_attribute("placeholder", field.placeholder)

        return el
```

---

## 5. Widget-to-Platform Mapping

### 5.1 Core Widget Mappings

| Widget | Browser HTML | Electron | VSCode Webview | TUI |
|--------|-------------|----------|----------------|-----|
| **Button** | `<button class="btn">` | Same as Browser | `<vscode-button>` | `[ Label ]` |
| **TextField** | `<input type="text">` | Same as Browser | `<vscode-text-field>` | `[________]` |
| **TextArea** | `<textarea>` | Same as Browser | `<vscode-text-area>` | Multi-line box |
| **Checkbox** | `<input type="checkbox">` | Same as Browser | `<vscode-checkbox>` | `[x]` / `[ ]` |
| **Radio** | `<input type="radio">` | Same as Browser | `<vscode-radio>` | `(*)` / `( )` |
| **Select** | `<select>` | Same as Browser | `<vscode-dropdown>` | `[v Option]` |
| **Slider** | `<input type="range">` | Same as Browser | Custom | `[====|----]` |
| **Progress** | `<progress>` | Same as Browser | `<vscode-progress-ring>` | `[████░░░░]` |
| **Link** | `<a href>` | Same as Browser | `<vscode-link>` | Underlined |
| **Badge** | `<span class="badge">` | Same as Browser | `<vscode-badge>` | `[N]` |
| **Tag** | `<span class="tag">` | Same as Browser | `<vscode-tag>` | `<tag>` |
| **Divider** | `<hr>` | Same as Browser | `<vscode-divider>` | `────────` |

### 5.2 Layout Widget Mappings

| Widget | Browser HTML | VSCode Webview | TUI |
|--------|-------------|----------------|-----|
| **Column** | `<div class="flex flex-col">` | Same | Vertical stack |
| **Row** | `<div class="flex flex-row">` | Same | Horizontal flow |
| **Grid** | `<div class="grid">` | Same | ASCII grid |
| **Stack** | `<div class="relative">` | Same | Layered |
| **Card** | `<div class="card">` | `<section>` + CSS | Box with border |
| **Panel** | `<div class="panel">` | `<vscode-panel-view>` | Box with title |
| **Tabs** | `<div role="tablist">` | `<vscode-panels>` | `[Tab1|Tab2|Tab3]` |
| **Tree** | `<ul class="tree">` | `<vscode-tree>` | Indented list |
| **Table** | `<table>` | `<vscode-data-grid>` | ASCII table |

### 5.3 VSCode-Specific Widgets

| Widget | VSCode Component | Purpose |
|--------|-----------------|---------|
| **PanelView** | `<vscode-panel-view>` | Tabbed panels |
| **DataGrid** | `<vscode-data-grid>` | Tables with sorting |
| **ProgressRing** | `<vscode-progress-ring>` | Loading spinner |
| **Panels** | `<vscode-panels>` | Tab container |

---

## 6. Electron/VSCode Integration Strategy

### 6.1 Electron Architecture

```
┌─────────────────────────────────────────────────────┐
│                   Electron App                       │
├─────────────────────────────────────────────────────┤
│  Main Process (Node.js)                             │
│  ┌─────────────────────────────────────────────────┐│
│  │  simple/std_lib/src/electron/                   ││
│  │  - app.spl (lifecycle)                          ││
│  │  - ipc.spl (messaging)                          ││
│  │  - tray.spl (system tray)                       ││
│  │  - power.spl (power events)                     ││
│  │  - fs_watcher.spl (file watching)               ││
│  │  - worker.spl (background tasks)                ││
│  └─────────────────────────────────────────────────┘│
├─────────────────────────────────────────────────────┤
│  Renderer Process (Chromium)                        │
│  ┌─────────────────────────────────────────────────┐│
│  │  Shared with Browser:                           ││
│  │  - HtmlRenderer                                 ││
│  │  - simple/std_lib/src/browser/dom.spl          ││
│  │  - simple/std_lib/src/browser/fetch.spl        ││
│  │                                                 ││
│  │  Electron-specific:                             ││
│  │  - IPC bridge to main process                   ││
│  │  - Native dialog access                         ││
│  │  - Clipboard access                             ││
│  └─────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────┘
```

### 6.2 VSCode Extension Architecture

```
┌─────────────────────────────────────────────────────┐
│                VSCode Extension                      │
├─────────────────────────────────────────────────────┤
│  Extension Host (Node.js)                           │
│  ┌─────────────────────────────────────────────────┐│
│  │  simple/std_lib/src/vscode/                     ││
│  │  - commands.spl (command registration)          ││
│  │  - languages.spl (language features)            ││
│  │  - window.spl (notifications, dialogs)          ││
│  │  - workspace.spl (file operations)              ││
│  └─────────────────────────────────────────────────┘│
├─────────────────────────────────────────────────────┤
│  Webview (Chromium sandbox)                         │
│  ┌─────────────────────────────────────────────────┐│
│  │  VscodeRenderer                                 ││
│  │  - VSCode Toolkit components                    ││
│  │  - Message passing via vscode.postMessage()     ││
│  │  - CSP restrictions                             ││
│  └─────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────┘
```

### 6.3 Unified Event Handling

```simple
# Event abstraction across platforms
enum PlatformEvent:
    Click(ElementId)
    Input(ElementId, String)
    Submit(ElementId)
    KeyPress(Key)
    Custom(String, Any)

trait EventHandler:
    fn handle(self, event: PlatformEvent)

# Browser/Electron: Direct DOM events
class BrowserEventBridge impl EventHandler:
    fn handle(self, event: PlatformEvent):
        match event:
            PlatformEvent.Click(id) =>
                self.element_handlers[id].on_click?()
            PlatformEvent.Input(id, value) =>
                self.element_handlers[id].on_change?(value)

# VSCode: Message passing
class VscodeEventBridge impl EventHandler:
    fn handle(self, event: PlatformEvent):
        # Events come from webview postMessage
        match event:
            PlatformEvent.Click(id) =>
                self.element_handlers[id].on_click?()
            PlatformEvent.Custom(type, data) =>
                self.custom_handlers[type]?(data)
```

---

## 7. API Consistency Guidelines

### 7.1 Naming Conventions

| Concept | Pattern | Example |
|---------|---------|---------|
| Widget creation | `WidgetName.new()` | `Button.new("Click")` |
| Property setter | `.property_name(value)` | `.disabled(true)` |
| Event handler | `.on_event(handler)` | `.on_click(fn(): ...)` |
| Style modifier | `.style_name(value)` | `.padding(8)` |
| Child addition | `.child(widget)` | `.child(Text.new("Hello"))` |
| Children batch | `.children([...])` | `.children([btn1, btn2])` |

### 7.2 State Management

```simple
# Reactive state (shared across templates and widgets)
class State[T]:
    value: T
    subscribers: List[fn(T)]

    fn get(self) -> T:
        return self.value

    fn set(mut self, new_value: T):
        self.value = new_value
        for sub in self.subscribers:
            sub(new_value)

    fn subscribe(mut self, handler: fn(T)):
        self.subscribers.append(handler)

# Usage in widget
let count = State.new(0)

fn build_counter() -> Widget:
    Column.new()
        .child(Text.new("Count: " + count.get().to_string()))
        .child(
            Button.new("+")
                .on_click(fn(): count.set(count.get() + 1))
        )
```

### 7.3 Theming

```simple
# Consistent theming across platforms
struct Theme:
    primary_color: Color
    secondary_color: Color
    background_color: Color
    text_color: Color
    font_family: String
    font_size: i32
    spacing_unit: i32
    border_radius: i32

# Platform-aware theme application
impl Theme:
    fn to_css(self) -> String:
        # Browser/Electron CSS variables
        return ":root { --primary: ${self.primary_color}; ... }"

    fn to_vscode_css(self) -> String:
        # Use VSCode CSS variables
        return ":root { --vscode-button-background: ${self.primary_color}; ... }"

    fn to_tui_palette(self) -> TuiPalette:
        # Terminal colors
        return TuiPalette { ... }
```

---

## 8. Implementation Roadmap

### Phase 1: Core Widget Library (2 weeks)
- [ ] Base `Widget` trait and `BuildContext`
- [ ] Layout widgets: Column, Row, Stack, Container
- [ ] Basic widgets: Button, Text, TextField
- [ ] HtmlRenderer implementation

### Phase 2: Platform Renderers (2 weeks)
- [ ] TuiRenderer with crossterm
- [ ] VscodeRenderer with VSCode Toolkit
- [ ] Event bridge abstraction

### Phase 3: Advanced Widgets (2 weeks)
- [ ] Select, Checkbox, Radio, Slider
- [ ] Table, Tree, Tabs
- [ ] Modal, Dialog, Toast

### Phase 4: Integration (1 week)
- [ ] State management integration
- [ ] Theme support
- [ ] Widget ↔ SUI template interop

---

## 9. File Locations

### Existing Files
- `src/ui/src/parser/ast.rs` - SuiTemplate AST (437 lines)
- `src/ui/src/render/backend.rs` - RenderBackend trait (48 lines)
- `simple/std_lib/src/browser/dom.spl` - Browser DOM (481 lines)
- `simple/std_lib/src/electron/*.spl` - Electron APIs (10 files, 1,252 lines)
- `simple/std_lib/src/vscode/*.spl` - VSCode APIs (4 files, 508 lines)

### Proposed New Files
```
simple/std_lib/src/ui/
├── __init__.spl           # Module exports
├── widget.spl             # Widget trait and base types
├── layout.spl             # Column, Row, Stack, Container, Grid
├── button.spl             # Button widget
├── input.spl              # TextField, TextArea, Select
├── display.spl            # Text, Icon, Image, Badge
├── container.spl          # Card, Panel, Modal
├── navigation.spl         # Tabs, Tree, Breadcrumb
├── feedback.spl           # Progress, Toast, Dialog
├── state.spl              # Reactive state management
├── theme.spl              # Theming system
└── render/
    ├── __init__.spl
    ├── html.spl           # Browser/Electron renderer
    ├── tui.spl            # Terminal renderer
    └── vscode.spl         # VSCode webview renderer
```

---

## 10. Conclusion

The recommended approach combines:

1. **Keep `.sui` templates** for page-level declarative UI (designer-friendly)
2. **Add Builder Pattern widgets** for reusable, composable components (developer-friendly)
3. **Platform-specific renderers** via `RenderBackend` trait (consistent API, native output)
4. **Unified event handling** across Browser, Electron, and VSCode
5. **Shared theming** with platform-aware CSS generation

This hybrid approach maximizes code reuse while respecting platform conventions.

---

## References

- [SwiftUI Documentation](https://developer.apple.com/documentation/swiftui)
- [Jetpack Compose](https://developer.android.com/jetpack/compose)
- [VSCode Webview UI Toolkit](https://github.com/microsoft/vscode-webview-ui-toolkit)
- [Electron Documentation](https://www.electronjs.org/docs)
- [Slint UI](https://slint.dev/)
- [Dioxus](https://dioxuslabs.com/)
