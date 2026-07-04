# Architecture Plan: Graphical Icon System for SimpleOS

## 1. Goal
Replace text-based Unicode icons and primitive-drawn shapes with a unified graphical icon system that works across baremetal (Compositor) and web (HTML) renderers.

## 2. Icon Format: Simple RLE (Run-Length Encoding)
Since we are in a memory-constrained environment, we will use a custom RLE format for icons.

```simple
struct IconDefinition:
    name: text
    width: i32
    height: i32
    rle_data: [u32] # [count, color, count, color, ...]
```

## 3. Core Components

### A. Rendering Primitives (`src/os/compositor/rendering_primitives.spl`)
Add `draw_icon_rle(backend, x, y, icon_def, scale)` function.

### B. Icon Registry (`src/lib/common/ui/icon_registry.spl`)
A central place to store and retrieve `IconDefinition` objects.
Includes icons for:
- **System**: Close, Minimize, Maximize, Search, WiFi, Battery.
- **Apps**: Terminal, File Manager, Calculator, Editor, Paint, Minesweeper, Tetris.
- **Files**: Folder, Document, Image, Code, Archive.

### C. UI Library Integration (`src/lib/common/ui/widget.spl`)
Update `WidgetNode` to support an `icon_id` property.
Update `builder.spl` to include `with_icon(id)` helper.

## 4. Implementation Phases

### Phase 1: Foundation
- Create `icon_registry.spl` with first set of RLE data (Stitch-aligned).
- Implement RLE renderer in `rendering_primitives.spl`.

### Phase 2: App Integration
- Refactor `file_manager.spl` to use graphical folder/file icons.
- Refactor `desktop_chrome.spl` to use graphical system icons.
- Update `paint.spl` tool icons.

### Phase 3: Extension
- Apply to `examples/` apps.
- Sync with GitHub.

## 5. Multiple Agent Tasks
- **Agent 1**: Implement RLE renderer and `IconRegistry`.
- **Agent 2**: Refactor `FileManager` and `DesktopChrome`.
- **Agent 3**: Update Creative/Game apps and examples.
