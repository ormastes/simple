# UI Render Feature Caret Architecture

## Purpose

This document defines the architecture for making render/export a shared UI
runtime feature rather than an app-local CLI flag.

The design follows existing repo direction:
- shared UI ownership under `src/app/ui/`
- MDSOC carets and configurable dimensions from `src/compiler/85.mdsoc/`
- layered UI placement precedent from `src/os/capsule.sdn`

---

## Problem

Current render and GUI launch semantics are split across:
- shared UI entrypoints
- app-local launchers
- example-local flags such as `smux --render`

This creates three kinds of drift:
1. parser drift
2. config drift
3. output/preview drift

---

## Feature-Caret Ownership Model

The render capability is represented as one feature caret: `ui.render`.

This feature id stays stable while responsibility is deployed through explicit
layers. Each layer owns a single concern and delegates to the next. Apps
participate as adapters at the bottom of the stack, not as independent render
authorities.

The caret model aligns with MDSOC because:
- carets already exist in the compiler
- layer orders and rules are already configurable
- transform-style bridges exist elsewhere in the repo
- UI already has a layered precedent in `src/os/capsule.sdn`

---

## Layer Responsibilities

| Layer | Responsibility | Owner |
|-------|----------------|-------|
| **Parser** | Parse CLI command and flags, validate combinations, populate typed config | `src/app/ui/cli_entry.spl` |
| **Config** | Typed `RenderConfig` with precedence rules, defaults, validation | `src/app/ui.render/types.spl` |
| **Session** | UI session creation, event replay, state capture | `src/app/ui.none/app.spl` |
| **Core** | Noninteractive render execution, state-to-output transformation | `src/app/ui.none/backend.spl` |
| **Export** | Text, HTML, and tree export; artifact generation | `src/app/ui.cli/`, `src/app/ui.tui_web/` |
| **Adapters** | App-specific view models and compatibility wrappers | `dashboard.render/`, `llm_dashboard/`, `office/` |

---

## Module Layout

```text
src/app/ui.render/
  __init__.spl          # Re-exports: RenderConfig, RenderRequest, RenderResult
  types.spl             # Contract types: RenderConfig, RenderRequest, RenderResult
  colors.spl            # Shared color definitions
  widgets.spl           # Widget render helpers (TUI + HTML)

src/app/dashboard.render/
  __init__.spl          # Dashboard render module init
  adapter.spl           # Dashboard adapter: metrics -> RenderResult
  colors.spl            # Dashboard-specific colors
  progress.spl          # Progress bar rendering
  table.spl             # Table rendering

src/app/llm_dashboard/
  render_adapter.spl    # LLM dashboard adapter

src/app/office/
  render_adapter.spl    # Office suite adapter (delegates to submodules)
  word/render.spl       # Word document rendering
  sheets/render.spl     # Spreadsheet rendering
  slides/render.spl     # Slide rendering
```

---

## Data Flow

```text
CLI args
  |
  v
Parser (cli_entry.spl)
  |  Validates flags, resolves --adapter, --format, --demo
  v
RenderConfig
  |  Typed config with precedence: defaults < feature config < env < CLI
  v
RenderRequest
  |  Config + export targets
  v
Session (ui.none/app.spl)
  |  Creates UI session, loads asset or adapter view model
  v
Core (ui.none/backend.spl)
  |  Executes noninteractive render, produces internal state
  v
Export (ui.cli/, ui.tui_web/)
  |  Transforms state to text, HTML, or both
  v
RenderResult
  |  .text_output, .html_output, .metadata, .warnings
  v
stdout / file output
```

---

## Type Contract

### RenderConfig

The single typed config object populated by the parser layer.

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `mode` | `text` | `"render"` | Adapter-specific mode |
| `backend` | `text` | `"auto"` | Backend hint |
| `format` | `text` | `"text"` | Output format: `text`, `html`, `both` |
| `width` | `i64` | `80` | Viewport width in columns |
| `height` | `i64` | `24` | Viewport height in rows |
| `theme` | `text` | `"dark"` | Theme name |
| `asset_path` | `text` | `""` | Path to `.ui.sdn` or data file |
| `adapter_name` | `text` | `""` | Which app adapter to use |
| `use_default_demo` | `bool` | `false` | Use built-in demo asset |

### RenderRequest

Combines config with export targets.

| Field | Type | Description |
|-------|------|-------------|
| `config` | `RenderConfig` | The render configuration |
| `export_targets` | `[text]` | List of export target paths |

### RenderResult

Output of a render operation.

| Field | Type | Description |
|-------|------|-------------|
| `format` | `text` | Which format was produced |
| `text_output` | `text` | Plain text rendering |
| `html_output` | `text` | HTML rendering |
| `metadata` | `Dict<text, text>` | Key-value metadata |
| `warnings` | `[text]` | Warnings encountered during render |

Factory methods: `RenderResult.empty()`, `RenderResult.text(content)`,
`RenderResult.html(content)`, `RenderResult.both(text, html)`.

---

## Configurability Model

Each layer-related value is configured through the shared `RenderConfig`
contract.

Precedence (highest wins):

1. CLI flags
2. Environment variables (`SIMPLE_RENDER_FORMAT`, `SIMPLE_GUI_BACKEND`)
3. Feature config file or module defaults
4. Built-in defaults (`RenderConfig.default()`)

The existing `SIMPLE_GUI_BACKEND` environment variable is one input to the
shared config model, not a parallel standalone system.

---

## Architectural Decisions

### Decision 1: Shared ownership

All common render/export behavior belongs to `src/app/ui.render/` and
`src/app/ui/`.

Per-app code may:
- provide assets
- provide adapter-specific view models
- provide compatibility shims

Per-app code must not:
- become the parser authority for shared render behavior
- define incompatible output semantics
- define new standalone render flags when delegation is possible

### Decision 2: Feature-caret model

Represent render as one feature caret (`ui.render`) deployed through explicit
layers. The same feature id stays stable while responsibility moves downward
through layers.

### Decision 3: Adapter backends

Backends are adapters over shared render data. Backends may choose how to
display or transport render output, but they do not own the meaning of
`render`, output format, default preview asset, or config precedence.

### Decision 4: Single parser authority

`src/app/ui/cli_entry.spl` is the parser authority for `simple ui`. Mode and
flag semantics flow from the same authoritative parse contract.

---

## How to Add a New Adapter

1. **Create the adapter module.** Add a `render_adapter.spl` file under your
   app directory (e.g. `src/app/myapp/render_adapter.spl`).

2. **Import shared types.** Use the contract types from `ui.render`:
   ```simple
   use app.ui.render.types.RenderConfig
   use app.ui.render.types.RenderResult
   ```

3. **Implement the render function.** Accept a `RenderConfig` and return a
   `RenderResult`:
   ```simple
   fn render(config: RenderConfig) -> RenderResult:
       var content = build_view_model(config)
       if config.format == "html":
           return RenderResult.html(to_html(content))
       return RenderResult.text(to_text(content))
   ```

4. **Register the adapter name.** Add an entry to the adapter dispatch table
   in the CLI parser so `--adapter myapp` resolves to your module.

5. **Add tests.** Validate that your adapter produces deterministic output for
   known inputs in both `text` and `html` formats.

---

## Migration Rules

1. No new app-local `--render` flags unless they delegate into shared UI.
2. New GUI-like apps must register a render adapter instead of inventing a new
   parser.
3. Default verification should use the shared demo asset
   (`examples/ui/widget_matrix.ui.sdn`).
4. Shared docs and tests must validate help/config/output parity.

---

## Proper UI Placement

Shared UI runtime logic belongs under:
- `src/app/ui/`
- `src/app/ui.render/`

App-specific UI business logic belongs under its app tree:
- `src/app/dashboard.render/`
- `src/app/llm_dashboard/`
- `src/app/office/`

Cross-cutting render/export behavior should not live in those app trees.

---

## Related Documents

- **Design**: `doc/05_design/ui_render_feature_caret.md`
- **Plan**: `doc/03_plan/ui_render_feature_caret_plan.md`
- **User guide**: `doc/07_guide/tooling/ui_render.md`
- **Shared types source**: `src/app/ui.render/types.spl`
