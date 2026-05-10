# UI Render Guide

## Purpose

`simple ui render` is the shared render/export surface for UI assets and
GUI-like apps. It produces deterministic text or HTML output from a single
command, suitable for Docker/headless environments, CI snapshots, and manual
inspection.

---

## Quick Start

```bash
# Render a .ui.sdn file as text
simple ui render examples/ui/widget_matrix.ui.sdn

# Render as HTML
simple ui render examples/ui/widget_matrix.ui.sdn --format html

# Render the built-in demo
simple ui render --demo

# Render dashboard adapter as HTML
simple ui render --adapter dashboard --format html

# Render office sheets as text
simple ui render --adapter sheets --format text
```

---

## Command

```text
simple ui render [file] [options]
```

If `file` is omitted and `--demo` is not set, the command prints usage help.

---

## Flags

| Flag | Default | Description |
|------|---------|-------------|
| `--format` | `text` | Output format: `text`, `html`, or `both` |
| `--adapter` | (none) | Adapter name (see below) |
| `--mode` | `render` | Adapter-specific mode (e.g. `status`, `text`, `render`) |
| `--theme` | `dark` | Theme name: `dark`, `light`, or adapter-specific |
| `--width` | `80` | Viewport width in columns |
| `--height` | `24` | Viewport height in rows |
| `--demo` | `false` | Use built-in demo asset (`examples/ui/widget_matrix.ui.sdn`) |
| `--backend` | `auto` | Backend hint: `auto`, `headless`, `tui`, `web`, `tauri`, `electron` |

---

## Adapters

Adapters bridge app-specific data into the shared render pipeline.

| Adapter | App | Description |
|---------|-----|-------------|
| `dashboard` | `src/app/dashboard.render/` | Project metrics dashboard |
| `llm_dashboard` | `src/app/llm_dashboard/` | LLM conversation dashboard |
| `word` | `src/app/office/word/` | Document renderer |
| `sheets` | `src/app/office/sheets/` | Spreadsheet renderer |
| `slides` | `src/app/office/slides/` | Presentation renderer |
| `mail` | `src/app/office/` | Email viewer (planned) |
| `planner` | `src/app/office/` | Task planner (planned) |
| `launcher` | `src/app/office/` | App launcher (planned) |

When `--adapter` is omitted, the command renders the `.ui.sdn` file directly
through the shared UI runtime.

---

## Format Options

| Format | Output |
|--------|--------|
| `text` | Plain text rendering suitable for terminals and CI logs |
| `html` | Standalone HTML document with inline CSS |
| `both` | Produces both text and HTML; text is printed to stdout, HTML is written to a `.html` file |

---

## Environment Variables

| Variable | Description |
|----------|-------------|
| `SIMPLE_RENDER_FORMAT` | Override default format (`text`, `html`, `both`). CLI `--format` takes precedence. |
| `SIMPLE_GUI_BACKEND` | Backend hint; feeds into the shared config model alongside `--backend`. |

Config precedence (highest wins):

1. CLI flags
2. Environment variables
3. Feature config
4. Built-in defaults

---

## Examples

### Render dashboard as HTML

```bash
simple ui render --adapter dashboard --format html
```

Produces an HTML report of current project metrics.

### Render office sheets as text

```bash
simple ui render --adapter sheets --format text --width 120
```

Produces a text table of spreadsheet contents at 120-column width.

### Use the built-in demo

```bash
simple ui render --demo --format both
```

Renders `examples/ui/widget_matrix.ui.sdn` in both formats. Useful for
verifying widget coverage and theme/layout regressions.

### Custom viewport and theme

```bash
simple ui render my_layout.ui.sdn --width 132 --height 43 --theme light
```

### Override format via environment

```bash
export SIMPLE_RENDER_FORMAT=html
simple ui render --demo
# Produces HTML output without --format flag
```

---

## Docker / Headless Usage

`simple ui render` works without a display server or raw terminal mode. It is
designed for headless environments such as Docker containers and CI runners.

```bash
# Inside Docker
docker run --rm simple-compiler:latest \
  simple ui render --demo --format html > report.html
```

### CI snapshot pattern

```bash
simple ui render --demo --format text > snapshots/widget_matrix.txt
diff snapshots/widget_matrix.txt snapshots/widget_matrix.expected.txt
```

### Container verification

```bash
simple ui render --adapter dashboard --format text
# Produces text output even without X11, Wayland, or a TTY
```

---

## Default Verification Asset

The default demo asset is:

```text
examples/ui/widget_matrix.ui.sdn
```

Use it when:
- validating widget rendering
- checking theme/layout regressions
- generating a known-good artifact for CI comparison

---

## Ownership Rules

Shared runtime ownership:
- `src/app/ui.render/` -- shared types and render primitives
- `src/app/ui/` -- CLI entry, parser, session

App-specific adapters:
- `src/app/dashboard.render/`
- `src/app/llm_dashboard/`
- `src/app/office/`

Rule: apps may adapt into shared render but should not redefine shared render
semantics. Do not add app-local `--render` flags when delegation into the
shared surface is possible.

---

## Troubleshooting

**No output produced**: Verify the file path exists and is a valid `.ui.sdn`
file. Use `--demo` to test with the built-in asset.

**HTML looks unstyled**: The `--theme` flag controls CSS generation. Try
`--theme dark` or `--theme light` explicitly.

**Adapter not found**: Check the adapter name spelling against the table above.
Planned adapters (mail, planner, launcher) are not yet available.

**Environment variable ignored**: CLI `--format` takes precedence over
`SIMPLE_RENDER_FORMAT`. Remove the CLI flag to use the environment variable.

---

## Source Code

- **Shared types**: `src/app/ui.render/types.spl`
- **Module exports**: `src/app/ui.render/__init__.spl`
- **Dashboard adapter**: `src/app/dashboard.render/adapter.spl`
- **LLM dashboard adapter**: `src/app/llm_dashboard/render_adapter.spl`
- **Office adapter**: `src/app/office/render_adapter.spl`
- **Design doc**: `doc/05_design/ui_render_feature_caret.md`
- **Architecture doc**: `doc/04_architecture/ui_render_feature_caret.md`
