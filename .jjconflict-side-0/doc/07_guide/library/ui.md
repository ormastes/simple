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

{$ let users: List[User] $}
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
extern fn rt_vk_device_create() -> u64
extern fn rt_vk_buffer_alloc(device: u64, size: u64) -> u64
extern fn rt_vk_buffer_upload(buffer: u64, data: *const u8, size: u64) -> i32
extern fn rt_vk_kernel_compile(device: u64, spirv: *const u8, len: u64) -> u64
extern fn rt_vk_kernel_launch_1d(...) -> i32
```

### Vulkan DSL

Simple reduces Vulkan verbosity by 95-98%:

```simple
import vulkan.{Device, Swapchain, Pipeline, Buffer}

fn main():
    window = Window.new("Vulkan Triangle", 800_600_size)
    device = Device.new()
    swapchain = Swapchain.new(device)
    pipeline = Pipeline.new().render_pass_from(swapchain)
    vertex_buffer = Buffer.vertex(VERTICES)

    while with window.frame() as frame:
        frame.draw(pipeline, vertex_buffer)
```

~20 lines vs ~1,000 in C++.

### Widget Systems

**GUI Widgets (Material Design):** Card, Chip, Avatar, Badge, Tooltip, Divider

**TUI Widgets:** Menu, Dialog, ProgressBar, TextInput, ScrollList

---

## Directory Structure

```
app/
  ui/
    pages/           # .page.sui files
    components/      # .ui.sui files
    layouts/         # Layout wrappers
  logic/
    pages/           # .spl paired logic
    components/
    layouts/
  assets/
    styles/base.css
    theme.tui.toml
```

---

## Related Files

- Web framework: `doc/07_guide/library/web_framework.md`
- Window SFFI: `src/app/io/window_ffi.spl`
- Graphics SFFI: `src/app/io/graphics2d_ffi.spl`
- Physics SFFI: `src/app/io/rapier2d_ffi.spl`
- Audio SFFI: `src/app/io/audio_ffi.spl`
- Gamepad SFFI: `src/app/io/gamepad_ffi.spl`
- Vulkan SFFI: `src/app/io/vulkan_ffi.spl`
