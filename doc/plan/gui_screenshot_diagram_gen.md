# GUI Screenshot and Diagram Generation for SSpec

## Overview

This document outlines the implementation of screenshot capture for GUI tests and Mermaid diagram generation for SSpec test documentation.

## Research Summary

### Current State

1. **SSpec Framework** (`simple/std_lib/src/spec/`)
   - Full BDD DSL with describe/context/it blocks
   - Test discovery via `*_spec.spl` pattern
   - Tag filtering support (e.g., `@slow`, `@integration`)
   - Diagram generation infrastructure exists (sequence, class, architecture)
   - No screenshot capture capability

2. **Test Runner** (`src/driver/src/cli/test_runner.rs`)
   - TestOptions struct with diagram options (seq_diagram, class_diagram, etc.)
   - Tag filtering via `--tag` option
   - Output directory support for diagrams

3. **Console Testing** (`simple/std_lib/src/spec/console/__init__.spl`)
   - PTY session management for terminal programs
   - Keyboard input simulation
   - Output capture and pattern matching
   - No screenshot capability

4. **TUI Framework** (`simple/std_lib/src/ui/tui/`)
   - Ratatui backend integration
   - Widget rendering
   - No screenshot capture

## Feature List

### Part 1: Screenshot Capture (Implement First)

#### 1.1 @gui Tag Support
- [ ] Add `@gui` tag detection in test discovery
- [ ] Support `@gui` in `__init__.spl` to mark entire directory
- [ ] Support `@gui` decorator on individual tests
- [ ] Support `@gui` comment annotation (`# @gui`)

#### 1.2 Screenshot Capture Module
- [ ] Create `simple/std_lib/src/spec/screenshot.spl`
- [ ] Capture before/after screenshots for GUI tests
- [ ] Support PTY buffer to ANSI-rendered image conversion
- [ ] Support Vulkan/GPU framebuffer capture
- [ ] Support TUI widget state capture

#### 1.3 Image Storage
- [ ] Default output: `doc/spec/image/`
- [ ] Maintain relative directory structure from test path
- [ ] File naming: `{test_name}_before.png`, `{test_name}_after.png`
- [ ] Track image metadata (hash, timestamp, test source)

#### 1.4 Refresh Options
- [ ] `--refresh-gui-image` option to force recapture all images
- [ ] Without flag: only capture new tests, skip existing
- [ ] Image change detection via hash comparison

#### 1.5 Markdown Integration
- [ ] Embed image links in generated spec markdown
- [ ] Show "Image not available" placeholder with generation instructions
- [ ] Format: `![Test Name](../image/path/test_before.png)`

### Part 2: Diagram Generation (Prepare Infrastructure)

#### 2.1 Diagram Types
- [ ] **Sequence Diagrams**: Method call flows from test execution
- [ ] **Class Diagrams**: Class relationships from traced calls
- [ ] **Architecture Diagrams**: Component interactions

#### 2.2 Diagram Configuration
```simple
struct DiagramConfig:
    diagram_type: DiagramType      # sequence, class, architecture
    include_patterns: List[String]  # Include filter
    exclude_patterns: List[String]  # Exclude filter
    link_to_test: Bool              # Link diagram to test case
    output_format: OutputFormat     # mermaid, plantuml
```

#### 2.3 Test-to-Diagram Linking
- [ ] Each diagram links to its source test
- [ ] Click-through from documentation to test source
- [ ] Bidirectional navigation

#### 2.4 Placeholder Generation
- [ ] Show "Diagram not available" when missing
- [ ] Include command to generate: `simple test --diagram-all path/to/spec.spl`

## Implementation Plan

### Phase 1: Screenshot Infrastructure (Current Task)

1. **Test Discovery Enhancement**
   - Add `@gui` tag parsing in `test_discovery.rs`
   - Check `__init__.spl` for directory-wide `@gui` flag

2. **Screenshot Module**
   ```simple
   # simple/std_lib/src/spec/screenshot.spl

   struct ScreenshotConfig:
       output_dir: PathBuf
       format: ImageFormat  # PNG, JPEG
       capture_mode: CaptureMode  # Before, After, Both

   fn capture_gui_state(name: String, config: ScreenshotConfig) -> ScreenshotResult
   fn capture_tui_buffer(session: ConsoleSession) -> Image
   fn render_ansi_to_image(buffer: String) -> Image
   ```

3. **Test Runner Integration**
   - Add `--refresh-gui-image` option
   - Track captured images per test
   - Store in `doc/spec/image/{relative_path}/`

4. **Markdown Generation**
   - Embed image links in generated documentation
   - Show placeholder with instructions for missing images

### Phase 2: Diagram Generation (Future Task)

1. **Profiling Integration**
   - Record method calls during test execution
   - Build call graph for sequence diagrams

2. **Mermaid Generation**
   ```mermaid
   sequenceDiagram
       participant Test
       participant UserService
       participant Database
       Test->>UserService: authenticate(user)
       UserService->>Database: query(sql)
       Database-->>UserService: Result
       UserService-->>Test: Bool
   ```

3. **Documentation Integration**
   - Embed diagrams in spec markdown
   - Link diagrams to test source code

## CLI Options

```bash
# Screenshot capture
simple test --tag gui                    # Run GUI tests only
simple test --refresh-gui-image          # Force recapture all images
simple test --gui-output doc/spec/image  # Custom output directory

# Diagram generation (future)
simple test --seq-diagram               # Generate sequence diagrams
simple test --class-diagram             # Generate class diagrams
simple test --arch-diagram              # Generate architecture diagrams
simple test --diagram-all               # Generate all diagram types
simple test --diagram-output doc/spec/diagrams
```

## File Structure

```
doc/spec/
├── image/                              # Screenshot images
│   ├── unit/
│   │   └── ui/
│   │       └── tui/
│   │           ├── widgets_spec/
│   │           │   ├── button_click_before.png
│   │           │   └── button_click_after.png
│   │           └── renderer_spec/
│   │               └── render_layout_after.png
│   └── integration/
│       └── console/
│           └── repl_spec/
│               └── completion_before.png
├── diagrams/                           # Mermaid diagrams (future)
│   └── sequence/
│       └── auth_flow.mmd
└── generated/
    └── tui_widgets.md                  # With embedded images/diagrams
```

## Image Placeholder Example

When image is not available:
```markdown
## Test: Button Click Behavior

> **Screenshot not available**
>
> To generate: `simple test --refresh-gui-image simple/std_lib/test/unit/ui/tui/widgets_spec.spl`

```

When image is available:
```markdown
## Test: Button Click Behavior

**Before:**
![Before button click](../image/unit/ui/tui/widgets_spec/button_click_before.png)

**After:**
![After button click](../image/unit/ui/tui/widgets_spec/button_click_after.png)
```

## Dependencies

### Required Crates (Rust side)
- `image` - Image manipulation
- `ansi-to-image` or custom ANSI renderer - Terminal buffer to image
- `vte` - Terminal escape sequence parsing

### Required Modules (Simple side)
- `std.spec.screenshot` - Screenshot capture API
- `std.spec.console` - Enhanced with screenshot support

## Status

- [x] Research and planning complete
- [x] Part 1: Screenshot capture implementation
  - [x] `@gui` tag detection in test discovery (`src/driver/src/cli/test_discovery.rs`)
  - [x] Screenshot capture module (`simple/std_lib/src/spec/screenshot.spl`)
  - [x] Image storage in `doc/spec/image/` with relative paths
  - [x] `--refresh-gui-image` option in test runner
  - [x] Markdown formatter with image links and placeholders
- [x] Part 2: Diagram generation infrastructure (prepared)
  - [x] Diagram module (`simple/std_lib/src/spec/diagram/__init__.spl`)
  - [x] Diagram integration module (`simple/std_lib/src/spec/diagram_integration.spl`)
  - [x] Mermaid generation for sequence, class, architecture diagrams
  - [x] Directory structure `doc/spec/diagrams/`
  - [x] Test runner integration (`src/driver/src/cli/test_runner.rs`)
  - [x] Exports in spec module (`simple/std_lib/src/spec/__init__.spl`)
  - [ ] Runtime FFI for actual diagram capture (future task)
