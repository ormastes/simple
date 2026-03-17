# UI Framework Guide

Covers `.sui` template files (server/client execution model, dual GUI+TUI renderer) and the GUI framework (windowing, 2D graphics, physics, audio, gamepad, GPU).

---

## .sui Template Architecture

```
Shared State {$ let x: T $}
    |
    +-- Server {- -}  (DB, session, auth)
    +-- Client {+ +}  (events, fetch, DOM)
    |
    v
Render Template {{ expr }}  {% code %}
    |
    +-- HTML String (SSR output)
    +-- PatchSet (incremental client updates)
        |
        +-- GUI Renderer (DOM/WebView)
        +-- TUI Renderer (Terminal)
```

---

## Template Syntax

| Syntax | Purpose | Runs on |
|--------|---------|---------|
| `{@ ... @}` | Directive (component/page declaration) | Compile-time |
| `{$ ... $}` | State declaration (shared) | Compile-time |
| `{- ... -}` | Server block (DB, session, auth) | Server only |
| `{+ ... +}` | Client block (events, fetch, DOM) | Client only |
| `{{ expr }}` | HTML-escaped output | Both |
| `{! expr !}` | Raw (unescaped) output | Both |
| `{% ... %}` | Control flow (if/for/let) | Both |
| `{# ... #}` | Comment | Neither |

### Counter Component

**UI File:** `app/ui/components/Counter.ui.sui`

```html
{@ component Counter @}

{$ let count: i32 $}

{- count = props.start or 0 -}

{+
  on_click("#inc", fn(): count += 1)
  on_click("#dec", fn(): count -= 1)
+}

<div class="counter">
  <button id="dec">-</button>
  <span>{{ count }}</span>
  <button id="inc">+</button>
</div>
```

**Logic File:** `app/logic/components/Counter.spl`

```spl
class Counter:
    fn reset():
        this.count = 0
        invalidate()
```

---

## Pages and Components

| Type | Extension | Purpose |
|------|-----------|---------|
| Page | `.page.sui` | Root mount point, routing entry, SSR |
| Component | `.ui.sui` | Reusable embedded element |

Every `.sui` file must have a paired `.spl` logic file:

```
app/ui/components/Counter.ui.sui
app/logic/components/Counter.spl   ->  class Counter { ... }
```

### Embedding Components

```html
{@ page Home @}

{$ let users: List<User> $}
{- users = UserService.list() -}

<main>
  {@ embed UserList users=users @}
  {@ embed SearchBox query="" hydrate="visible" @}
</main>
```

### Hydration Strategies

| Strategy | When |
|----------|------|
| `hydrate="load"` | Immediately on page load (default) |
| `hydrate="visible"` | When scrolled into viewport |
| `hydrate="idle"` | During browser idle time |
| `hydrate="interaction"` | On first user interaction |
| `hydrate="none"` | Never (static only) |

---

## Server and Client Blocks

### Server Block (`{- -}`)

Runs once during SSR. Access to DB, sessions, file system.

```html
{-
  let session = get_session(request)
  let user = db.find_user(session.user_id)
  let posts = db.query("SELECT * FROM posts WHERE author = ?", user.id)
-}
```

### Client Block (`{+ +}`)

Runs after hydration in browser. Access to DOM events, fetch, local storage.

```html
{+
  on_click("#load-more", async fn():
    let more = await fetch_json("/api/posts?page=" + page)
    posts = posts.concat(more)
    invalidate()
  )

  on_input("#search", fn(e):
    filter = e.target.value
    invalidate()
  )
+}
```

### Control Flow

```html
{% if user.is_admin: %}
  <button>Delete All</button>
{% else: %}
  <span>Read only</span>
{% end %}

<ul>
  {% for item in items: %}
    <li key="{{ item.id }}">{{ item.name }}</li>
  {% end %}
</ul>
```

---

## Layouts and Slots

**Define layout:**

```html
{@ layout AppShell @}
{$ let title: str $}

<html>
  <head><title>{{ title }} - MyApp</title></head>
  <body>
    <nav>{@ slot nav @}</nav>
    <main>{@ slot main @}</main>
  </body>
</html>
```

**Use layout:**

```html
{@ page Home layout=AppShell title="Home" @}

{@ fill nav @}
  <a href="/">Home</a>
  <a href="/about">About</a>
{@ end @}

{@ fill main @}
  <h1>Welcome!</h1>
{@ end @}
```

---

## Dual Renderer: GUI + TUI

The same `.sui` compiles to both graphical and terminal output.

| Sui Element | GUI | TUI |
|-------------|-----|-----|
| `<div>` | `<div>` | Box |
| `<button>` | `<button>` | `[ Label ]` |
| `<input>` | `<input>` | `[________]` |
| `<ul>/<li>` | List | Bulleted lines |
| `<table>` | Table | ASCII table |

TUI uses a subset of CSS (flex, padding, margin) and keyboard navigation.

---

## GUI Framework

A complete graphics framework built on production-grade Rust libraries via SFFI.

### Component Stack

| Component | Library | Extern Fns | Purpose |
|-----------|---------|------------|---------|
| Windowing | Winit | 63 | Window management, events, input |
| 2D Graphics | Lyon | 57 | Vector tessellation, shapes |
| Physics | Rapier2D | 52 | Rigid body dynamics, collisions |
| Audio | Rodio | 40+ | Playback, spatial audio |
| Gamepad | Gilrs | 30+ | Controller input, rumble |
| GPU Compute | Vulkan | 47 | SPIR-V compilation, GPU buffers |

### Windowing (Winit)

```simple
val event_loop = window_create_event_loop()
val window = window_create(event_loop, 800, 600, "My App")

# Event types: WindowResized, KeyboardInput, MouseButton,
#              MouseMoved, MouseWheel, TouchEvent, etc.
window_poll_events(event_loop)
```

Configuration includes size, position, resizable, fullscreen, decorations, transparency, cursor control, and clipboard access.

### 2D Graphics (Lyon)

GPU-based vector graphics tessellation:

```simple
val builder = graphics_path_builder_new()
graphics_path_begin(builder, Point2D(x: 0.0, y: 0.0))
graphics_path_line_to(builder, Point2D(x: 100.0, y: 0.0))
graphics_path_close(builder)
val path = graphics_path_build(builder)

val fill = graphics_fill_tessellate(path, 0.1)
val vertices = graphics_fill_get_vertices(fill)
val indices = graphics_fill_get_indices(fill)
# Upload to GPU and render
```

Shape primitives: Rectangle, Circle, Ellipse, Polygon, Star. Stroke options: line caps (Butt, Square, Round), line joins (Miter, Round, Bevel).

### Physics (Rapier2D)

```simple
val world = physics_create_world(Vector2(x: 0.0, y: -9.81))

# Create rigid bodies (Dynamic, Static, Kinematic)
# Add colliders (Circle, Box, Capsule, Polygon)
# Detect collisions, raycasting

physics_step(world, 1.0 / 60.0)    # 60 FPS timestep
```

### Audio (Rodio)

Formats: WAV, MP3, OGG, FLAC. Features: play/pause/stop, volume, speed, loop, seek, spatial 3D positioning.

### Gamepad (Gilrs)

Cross-platform controller input: button states, axis values (sticks, triggers), D-pad, rumble/vibration. Poll-based event queue.

### GPU Compute (Vulkan)

Compiles Simple MIR to SPIR-V bytecode for GPU execution:

```simple
extern fn rt_vulkan_init() -> bool
extern fn rt_vulkan_alloc_buffer(size: i64, usage: i64) -> i64
extern fn rt_vulkan_compile_spirv(spirv_bytes: [u8]) -> i64
extern fn rt_vulkan_create_compute_pipeline(shader_module: i64, entry_point: text, push_constant_size: i64) -> i64
extern fn rt_vulkan_dispatch(cmd: i64, x: i64, y: i64, z: i64) -> bool
```

### Vulkan DSL

Simple reduces Vulkan verbosity by 95-98% using Tier 2 wrappers:

```simple
import gc_async_mut.io.vulkan_ffi.{vulkan_init, vulkan_alloc_storage,
    vulkan_compile_glsl, vulkan_create_pipeline, vulkan_begin_compute,
    vulkan_cmd_bind_pipeline, vulkan_cmd_dispatch, vulkan_submit_and_wait}

fn main():
    vulkan_init()
    val buf = vulkan_alloc_storage(1024)
    val shader = vulkan_compile_glsl(compute_shader_source)
    val pipe = vulkan_create_pipeline(shader, "main")
    val cmd = vulkan_begin_compute()
    vulkan_cmd_bind_pipeline(cmd, pipe)
    vulkan_cmd_dispatch(cmd, 16, 1, 1)
    vulkan_submit_and_wait(cmd)
```

~15 lines vs ~1,000 in C++.

### Widget Systems

**GUI Widgets (Material Design):** Card, Chip, Avatar, Badge, Tooltip, Divider

**TUI Widgets:** Menu, Dialog, ProgressBar, TextInput, ScrollList

---

## SDN Declarative UI Format

The `.ui.sdn` format defines UIs declaratively using Simple's SDN data format. Parsed by `src/lib/common/ui/parse/sdn.spl`.

### Minimal Example

```sdn
app:
  title: "Minimal"
  theme: dark

keybindings:
  normal:
    q: quit

layout:
  type: vbox
  children:
    - type: panel
      id: main
      title: Hello
      flex: 1
      children:
        - type: text
          id: greeting
          content: "Hello from Simple UI!"
    - type: statusbar
      id: status
      left: "{app.mode} MODE"
      right: "{app.title}"
```

### Available Widget Types

| Widget | Description |
|--------|-------------|
| `vbox` | Vertical box layout |
| `hbox` | Horizontal box layout |
| `panel` | Bordered panel with title |
| `text` | Text display |
| `progress` | Progress bar |
| `statusbar` | Status bar with left/right sections |
| `menubar` | Menu bar |
| `list` | Selectable list |

See `examples/ui/` for working examples.

---

## Directory Structure

```
src/lib/common/ui/       # Core shared UI library
  widget.spl             # WidgetNode, WidgetKind, UITree
  layout.spl             # Layout engine (HBox, VBox, Grid)
  state.spl              # State management
  backend.spl            # RenderBackend trait
  builder.spl            # Fluent builder API
  style.spl              # Theming and styling
  reactive.spl           # Reactive bindings
  event.spl              # Event types
  mode.spl               # UI mode (normal, insert, command)
  diff.spl               # Tree diffing
  patch.spl              # Patch application
  parse/sdn.spl          # .ui.sdn file parser
  parse/html.spl         # HTML-like markup parser

src/app/ui.core/         # App-level types, parser, state
src/app/ui.render/       # Widget rendering (TUI + HTML)
src/app/ui.tui/          # TUI backend (screen, input, app loop)
src/app/ui.web/          # Web backend (HTML gen, WebSocket, server)
src/app/ui.vscode/       # VSCode webview backend
src/app/ui.electron/     # Electron desktop backend
src/app/ui.mcp/          # MCP tool integration

examples/ui/             # Working UI examples (.ui.sdn)
```

---

## Related Files

- Web framework: `doc/guide/library/web_framework.md`
- Window SFFI: `src/lib/nogc_sync_mut/io/window_ffi.spl`
- Graphics SFFI: `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl`
- Physics SFFI: `src/lib/nogc_sync_mut/io/rapier2d_ffi.spl`
- Audio SFFI: `src/lib/nogc_sync_mut/io/audio_ffi.spl`
- Gamepad SFFI: `src/lib/nogc_sync_mut/io/gamepad_ffi.spl`
- Vulkan SFFI: `src/lib/gc_async_mut/io/vulkan_ffi.spl`
- UI core library: `src/lib/common/ui/`
- UI backends: `src/app/ui.tui/`, `src/app/ui.web/`, `src/app/ui.vscode/`, `src/app/ui.electron/`
- UI examples: `examples/ui/`
