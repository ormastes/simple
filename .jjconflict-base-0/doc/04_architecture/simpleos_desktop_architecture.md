# SimpleOS Desktop Architecture

The SimpleOS desktop environment provides a full graphical shell with 29 built-in applications. All apps and the shell itself use the MDSOC+ pattern (MDSOC capsule outside, ECS/UISession inside) with a shared widget builder DSL.

## Stack Overview

```
+--------------------------------------------------+
|  Desktop Apps (29)                                |
|  calculator, editor, terminal, browser, paint,    |
|  settings, file_manager, games, etc.             |
+--------------------------------------------------+
|  Desktop Shell (src/os/desktop/)                  |
|  shell.spl, taskbar, app_launcher, app_switcher   |
+--------------------------------------------------+
|  Compositor (src/os/compositor/)                  |
|  WindowSurface, z-order, Engine2D backend         |
+--------------------------------------------------+
|  UI Framework (src/lib/common/ui/)                |
|  WidgetNode, UISession, builder DSL, layout,      |
|  events, lifecycle, reactive state, accessibility |
+--------------------------------------------------+
|  Engine2D (src/lib/gc_async_mut/gpu/engine2d/)    |
|  draw_rect, draw_text, fill_rect, draw_line       |
+--------------------------------------------------+
|  Framebuffer Driver (src/os/drivers/framebuffer/) |
+--------------------------------------------------+
```

## Compositor

The compositor (`src/os/compositor/compositor.spl`) manages window surfaces and composites them for display.

**Key types:**

- `WindowSurface` -- represents a single window with position, size, z-order, and content tree
- `Compositor` -- owns all window surfaces, handles z-ordering and input routing

**Key operations:**

- `create_window_with_tree(title, x, y, width, height, tree)` -- creates a new window surface from a UITree
- `window_process_id(id)` / `window_app_id(id)` -- metadata lookup
- `window_count_for_process(process_id)` / `windows_for_process(process_id)` -- process window enumeration

**Backends:**

- `compositor_engine2d.spl` -- Engine2D-based rendering backend
- `browser_compositor_backend.spl` -- deterministic software compositor for WM capture tests

## Desktop Shell

The desktop shell (`src/os/desktop/shell.spl`) provides the taskbar, app launcher, and app lifecycle management.

**Imports:**

```
use common.ui.session.{UISession, new_session}
use common.ui.builder.{column, row, panel, text_widget, button, label, statusbar, build_tree, build_tree_with_title, ...}
use os.compositor.compositor.{Compositor, WindowSurface}
use os.desktop.app_manifest.{AppManifest, load_app_manifests, search_apps, manifest_categories}
use std.gc_async_mut.gpu.engine2d.engine.{Engine2D}
```

**Key functions:**

- `launch_app_baremetal(name)` -- launches an app by name, creates its UISession, registers its window with the compositor
- `_draw_baremetal_overlay(...)` -- renders the compositor overlay (taskbar, window decorations) using Engine2D

**Shell components** (`src/os/desktop/`):

| File | Purpose |
|------|---------|
| `shell.spl` | Main desktop shell, window management loop |
| `app_manifest.spl` | Application manifest definitions and loading |
| `app_switcher.spl` | Alt-Tab style app switching |
| `dock.spl` | Dock/launcher bar |
| `notification_center.spl` | Notification display |
| `taskbar_shell.spl` | Taskbar rendering |
| `z_order_store.spl` | Window z-order state |

## Widget Builder DSL

The widget builder (`src/lib/common/ui/builder.spl`) provides a fluent API for constructing widget trees without SDN/HTML files.

**Usage example:**

```
val ui = column("main",
    menubar("menu", ["File", "Edit", "View"]),
    row("content",
        panel("sidebar", text("nav", "Navigation")),
        panel("editor", input("search", "Search..."))
    ),
    statusbar("status", "{app.mode}", "{app.title}")
)
```

**Container builders:** `column`, `row`, `grid`, `panel`

**Leaf widget builders:** `text_widget`, `label`, `button`, `checkbox`, `dropdown`, `text_field`, `image`, `divider`, `dialog`, `tooltip`, `progress`, `input`

**Composite builders:** `menubar`, `menubar_rich`, `menu_separator`, `menu_with_submenu`, `statusbar`, `tabs`, `list_widget`, `table_widget`, `table_row`

**Tree/scroll builders:** `tree_widget`, `tree_node`, `tree_leaf`, `scroll`, `textarea`

**Tree construction:** `build_tree` (returns UITree), `build_tree_with_title` (returns UITree with window title)

**Widget modifiers:** `with_flex`, `with_width`, `with_height`, `with_visible`, `with_selected`, `with_disabled`, `with_readonly`, `with_error`, `with_validator`, `with_required`, `with_max_length`, `with_tooltip_text`

**Lifecycle hook modifiers:** Lifecycle callback attachment for widget events.

**Responsive/adaptive builders:** Per-size-class layouts (`responsive_compact`, `responsive_regular`, `responsive_expanded`), orientation-aware visibility (`show_when_at_most`, `show_when_at_least`, `show_when_orientation`).

## UISession Pattern

Every app builds a UISession, which serves as the ECS World in the MDSOC+ pattern:

| MDSOC+ Concept | UI Equivalent |
|----------------|---------------|
| Component | `WidgetNode` / `WidgetRecord` -- immutable widget description |
| Entity | Node ID (`u64`) -- stable within a session |
| World | `UISession` -- owns entity registry + component stores |
| System | `UIEventBus`, layout engine, lifecycle dispatcher |
| Query | Typed iterator over nodes with given props/style |
| Change Detection | `Added<WidgetNode>` / `Changed<WidgetRecord>` |

**App pattern:**

```
class Calculator:
    static fn new() -> Calculator: ...
    me build_ui() -> UISession:
        val tree = build_tree_with_title("Calculator",
            column("main",
                panel("display", ...),
                row("buttons", ...)
            )
        )
        return new_session(tree)
```

## Engine2D Draw Primitives

The Engine2D (`src/lib/gc_async_mut/gpu/engine2d/`) provides 2D rendering used by both the compositor and apps:

- `draw_rect`, `fill_rect` -- rectangle drawing and filling
- `draw_text` -- text rendering
- `draw_line` -- line drawing
- Used by compositor for window decorations, taskbar, and overlay rendering

## App Registration

**App manifest** (`src/os/desktop/app_manifest.spl`):

- `AppManifest` struct -- metadata: app ID, display name, icon, description, category
- `UiBackendKind` enum -- `Electron`, `SimpleWeb`, `Auto`
- `HostCaps` struct -- runtime-detected capabilities for backend selection
- `resolve_backend(manifest, caps)` -- selects rendering backend based on host capabilities
- `load_app_manifests()` -- loads all registered app manifests
- `search_apps(query)` / `manifest_categories()` -- app discovery
- `default_manifests()` -- built-in default app list

SimpleOS rejects Electron at manifest-load time (no Node/Chromium in kernel).

## Desktop Apps (29)

All apps in `src/os/apps/`:

| App | Description |
|-----|-------------|
| `browser_demo` | Browser engine demo |
| `calculator` | Calculator |
| `calendar` | Calendar |
| `clock` | Clock/timer |
| `color_picker` | Color picker tool |
| `contacts` | Contact manager |
| `disk_manager` | Disk management |
| `editor` | Text editor |
| `file_explorer` | File explorer |
| `file_manager` | File manager |
| `font_viewer` | Font preview |
| `hello_world` | Hello world demo |
| `hex_editor` | Hex editor |
| `image_viewer` | Image viewer |
| `installer_gui` | GUI installer |
| `log_viewer` | Log viewer |
| `memo` | Memo/notes |
| `minesweeper` | Minesweeper game |
| `network_monitor` | Network monitoring |
| `package_manager` | Package manager GUI |
| `paint` | Paint/drawing app |
| `screenshot` | Screenshot capture |
| `settings` | System settings |
| `snake` | Snake game |
| `solitaire` | Solitaire card game |
| `system_monitor` | System resource monitor |
| `terminal` | Terminal emulator |
| `tetris` | Tetris game |
| `todo` | Todo list manager |

Each app follows the same pattern: imports `common.ui.session.{UISession}` and `common.ui.builder.{...}`, defines a class with a `build_ui() -> UISession` method that constructs the widget tree using the builder DSL.
