# SimpleOS Desktop Applications

SimpleOS ships with 30 desktop applications located under `src/os/apps/`. Each app follows a consistent widget builder DSL pattern and integrates with the desktop shell via the launcher and compositor.

---

## Application Catalog

### Productivity

| App | Directory | Description |
|-----|-----------|-------------|
| Calculator | `src/os/apps/calculator/` | Standard calculator with arithmetic operations |
| Calendar | `src/os/apps/calendar/` | Date viewer and calendar |
| Clock | `src/os/apps/clock/` | Clock with stopwatch and timer |
| Contacts | `src/os/apps/contacts/` | Contact list manager |
| Memo | `src/os/apps/memo/` | Quick note-taking |
| Todo | `src/os/apps/todo/` | Task list manager |

### Editors and Viewers

| App | Directory | Description |
|-----|-----------|-------------|
| Text Editor | `src/os/apps/editor/` | Plain text editor |
| Hex Editor | `src/os/apps/hex_editor/` | Binary/hex file editor |
| Image Viewer | `src/os/apps/image_viewer/` | Image display and browsing |
| Font Viewer | `src/os/apps/font_viewer/` | System font preview |
| Paint | `src/os/apps/paint/` | Bitmap drawing application |
| Color Picker | `src/os/apps/color_picker/` | RGB/Hex color selection tool |

### System Utilities

| App | Directory | Description |
|-----|-----------|-------------|
| Terminal | `src/os/apps/terminal/` | Command-line terminal emulator |
| File Manager | `src/os/apps/file_manager/` | File browsing and management |
| File Explorer | `src/os/apps/file_explorer/` | Tree-based file navigation |
| Settings | `src/os/apps/settings/` | System settings and preferences |
| System Monitor | `src/os/apps/system_monitor/` | CPU, memory, and process monitoring |
| Disk Manager | `src/os/apps/disk_manager/` | Disk partitions and storage management |
| Log Viewer | `src/os/apps/log_viewer/` | System log viewer |
| Network Monitor | `src/os/apps/network_monitor/` | Network status and traffic monitoring |
| Screenshot | `src/os/apps/screenshot/` | Screen capture utility |
| Package Manager | `src/os/apps/package_manager/` | Package installation and updates |

### System Setup

| App | Directory | Description |
|-----|-----------|-------------|
| Installer GUI | `src/os/apps/installer_gui/installer_gui.spl` | OS installation wizard |
| Upgrade GUI | `src/os/apps/installer_gui/upgrade_gui.spl` | OS upgrade wizard |
| Hello World | `src/os/apps/hello_world/` | Minimal example application |

### Games

| App | Directory | Description |
|-----|-----------|-------------|
| Minesweeper | `src/os/apps/minesweeper/` | Classic minesweeper game |
| Snake | `src/os/apps/snake/` | Snake game |
| Tetris | `src/os/apps/tetris/` | Tetris game |
| Solitaire | `src/os/apps/solitaire/` | Card solitaire game |

### Web

| App | Directory | Description |
|-----|-----------|-------------|
| Browser Demo | `src/os/apps/browser_demo/` | Minimal browser demonstration |

---

## Entry Point Pattern

Every SimpleOS app follows the same two-method pattern:

```simple
use common.ui.widget.{WidgetNode, UITree}
use common.ui.session.{UISession}
use common.ui.builder.{column, row, panel, text_widget, button, label, statusbar, build_tree_with_title}

class MyApp:

    static fn new() -> MyApp:
        MyApp()

    me build_ui() -> UISession:
        # Build widget tree using the builder DSL
        val root = column("root", [
            # ... widgets ...
        ])
        val tree = build_tree_with_title(root, "My App", "dark")
        UISession.new(tree)
```

- `static fn new() -> ClassName` -- constructor, returns a new instance
- `me build_ui() -> UISession` -- builds the widget tree and returns a UI session

---

## Widget Builder DSL

Apps construct their UI using composable builder functions from `common.ui.builder`. Each function takes an ID string, and either a label/content string or a list of child widgets.

### Layout Containers

| Function | Signature | Description |
|----------|-----------|-------------|
| `column` | `column(id, children)` | Vertical stack layout |
| `row` | `row(id, children)` | Horizontal row layout |
| `panel` | `panel(id, title, children)` | Titled panel container |

### Leaf Widgets

| Function | Signature | Description |
|----------|-----------|-------------|
| `text_widget` | `text_widget(id, content)` | Read-only text display |
| `label` | `label(id, text)` | Static label |
| `button` | `button(id, label, action)` | Clickable button with action identifier |
| `statusbar` | `statusbar(id, text)` | Status bar at bottom |

### Tree Construction

| Function | Signature | Description |
|----------|-----------|-------------|
| `build_tree_with_title` | `build_tree_with_title(root, title, theme)` | Wrap root node into a UITree with window title and theme |

### Example: Calculator

```simple
use common.ui.widget.{WidgetNode, UITree}
use common.ui.session.{UISession}
use common.ui.builder.{column, row, panel, text_widget, button, label, statusbar, build_tree_with_title}

class Calculator:

    static fn new() -> Calculator:
        Calculator()

    me build_ui() -> UISession:
        val display = panel("calc_display", "Calculator", [
            text_widget("display_value", "0"),
            text_widget("display_expr", "")
        ])

        val row_789 = row("row_789", [
            button("btn_7", "7", "calc.digit.7"),
            button("btn_8", "8", "calc.digit.8"),
            button("btn_9", "9", "calc.digit.9"),
            button("btn_mul", "*", "calc.op.mul")
        ])

        val keypad = panel("keypad", "Keypad", [
            row_789
            # ... more rows ...
        ])

        val root = column("calc_root", [
            display,
            keypad
        ])

        val tree = build_tree_with_title(root, "Calculator", "dark")
        UISession.new(tree)
```

---

## Desktop Shell Integration

### App Manifest

Each app is registered with the desktop shell via `AppManifest` (defined in `src/os/desktop/app_manifest.spl`):

```simple
struct AppManifest:
    name: text              # Display name
    description: text       # Short description
    category: text          # "System", "Utilities", "Development", "Settings"
    binary: text            # Path to binary
    capabilities: [text]    # Required capabilities
    icon: text              # Icon identifier
    app_class: AppClass
    fault_domain: AppFaultDomain
    supervisor_policy: SupervisorPolicy
```

Manifests can be loaded from `/usr/share/apps/*.sdn` or returned as built-in defaults.

### Desktop Shell

The desktop shell (`src/os/desktop/shell.spl`) imports all apps and manages:

- **Taskbar** -- window list, clock, system tray (pinned to screen bottom)
- **App Launcher** -- starts apps from manifests
- **Compositor integration** -- window surfaces, z-ordering, focus management

The shell imports each app class and dispatches via the launcher service:

```simple
use os.apps.calculator.calculator.{Calculator}
use os.apps.clock.clock.{ClockApp}
use os.apps.terminal.terminal.{Terminal}
# ... all 30 apps imported ...
```

### Related Files

| File | Purpose |
|------|---------|
| `src/os/desktop/shell.spl` | Desktop shell, imports and launches all apps |
| `src/os/desktop/app_manifest.spl` | AppManifest struct and loading |
| `src/os/desktop/taskbar_shell.spl` | Taskbar rendering |
| `src/os/desktop/dock.spl` | Application dock |
| `src/os/desktop/app_switcher.spl` | Alt-Tab app switching |
| `src/os/desktop/notification_center.spl` | Notification center |
| `src/os/desktop/z_order_store.spl` | Window z-order management |

---

## See Also

- [UI Stack Guide](ui_stack_guide.md) -- full UI rendering stack
- [SimpleOS Dev Guide](platform/simpleos_dev_guide.md) -- SimpleOS tooling, bootstrap, build and run
- [Library UI Guide](library/ui.md) -- UI framework (.sui files)
- [Stitch SimpleOS Theme](theme/stitch_simple_os_theme.md) -- theme design tokens
