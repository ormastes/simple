# Detail Design: Simple Theme System

## 1. File Format: `.simple-theme`

The format is a standard CSS file with a header comment for Stitch metadata.

```css
/*
@stitch.project: 12496218458601315145
@stitch.display_name: SimpleOS Obsidian
@stitch.color_mode: DARK
*/

:root {
  /* Core UI Variables */
  --ui-bg: #12121f;
  --ui-fg: #e3e0f3;
  --ui-accent: #c6c6c8;
  --ui-border-radius: 8px;

  /* Glassmorphism Variables */
  --glass-surface: rgba(18, 18, 31, 0.72);
  --glass-blur: 20px;
  --glass-border: rgba(149, 142, 152, 0.15);
}
```

## 2. SimpleTheme Class Implementation

Located in `src/lib/common/ui/simple_theme.spl`.

```simple
class SimpleTheme:
    name: text
    metadata: StitchMetadata
    tokens: GlassDesignTokens

    static fn from_css(name: text, css: text) -> SimpleTheme:
        # 1. Extract metadata from comments
        # 2. Extract variables via regex/lexer
        # 3. Construct objects
        pass_todo("Implement CSS parser")

    me to_css() -> text:
        # 1. Emit metadata header
        # 2. Emit :root block with variables
        pass_todo("Implement CSS emitter")
```

## 3. Integration with ThemeService

The `ThemeService` will now support loading themes from files:

```simple
me load_theme_file(path: text):
    val css = rt_file_read_text(path)
    val name = path.filename_without_extension()
    val theme = SimpleTheme.from_css(name, css)
    self.active_theme = theme
    self.notify_all()
```

## 4. Agent Tasks

- [ ] Task 1: Create `SimpleTheme` class and CSS parser/emitter.
- [ ] Task 2: Update `ThemeService` to load `.simple-theme` files.
- [ ] Task 3: Update `theme-sync` to pull/push using `.simple-theme` format.
- [ ] Task 4: refactor `Compositor` to initialize from `SimpleTheme` tokens.
