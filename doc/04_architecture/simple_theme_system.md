# Architecture: Simple Theme System

## 1. Unified Theme Core

### SimpleTheme Class
A central container that bridges multiple styling domains.

```simple
class SimpleTheme:
    name: text
    css_source: text              # Original CSS content
    base: UITheme                 # Core colors, spacing
    glass: GlassDesignTokens      # Glassmorphism tokens
    stitch: StitchMetadata        # Round-trip metadata
```

## 2. Transformation Pipeline

### CSS to SimpleTheme (Parser)
- Reads `.simple-theme` file.
- Extracts `--ui-*` variables for `UITheme`.
- Extracts `--glass-*` variables for `GlassDesignTokens`.
- Extracts `/* @stitch ... */` annotations for metadata.

### SimpleTheme to CSS (Emitter)
- Generates standard CSS block with all variables.
- Includes Stitch metadata as comments.

### SimpleTheme to Numeric (Baremetal)
- Converts hex/rgba strings to `u32` colors and `i32` dimensions.
- Populates `GlassConfig` for the compositor.

## 3. Round-Trip with Stitch

### Pull Path
1. `theme-sync pull` downloads Stitch SDN snapshot.
2. `ParsedStitchDesignSystem` is converted to `SimpleTheme`.
3. `.simple-theme` file is overwritten with new CSS.

### Push Path
1. `theme-sync push` reads `.simple-theme`.
2. Parsed variables are mapped back to `StitchMd3Colors` and `StitchMetadata`.
3. Stitch update payload is generated and dispatched.

## 4. Integration Points

- **Simple GUI Library**: Each widget uses `me style() -> text` which references CSS variables from the active `SimpleTheme`.
- **Simple Window Manager**: Loads `active.simple-theme` at boot and initializes `GlassConfig`.
- **Web WM**: `app.ui.web.html.generate_css(theme)` emits the shared CSS variables and WM chrome classes directly into the HTML shell.
- **Simple Web Renderer**: `browser_engine/style_block.spl` parses embedded `<style>` blocks and resolves `var(--token)` values so CSS-only theme changes affect rendered pixels.
- **Electron Snapshot Export**: `tools/electron-shell/export_snapshot.js --no-fallback` validates the strict IPC path; without `--no-fallback`, the exporter falls back to the shared HTML generator while keeping the same CSS output path.
