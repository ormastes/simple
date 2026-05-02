# Local Research: Shared UI Render Feature Caret

**Date:** 2026-04-03
**Scope:** shared `simple ui render` surface, parser/config auto-attachment, MDSOC-aligned feature-caret deployment, and migration path for GUI-like apps.

## Summary

The repo already contains almost all primitives needed for a common `render`
feature. The problem is ownership, not capability.

Today:
- shared UI entry and backend detection live under `src/app/ui/`
- headless capture and textual observers already exist
- some apps still parse GUI/render flags locally
- there is no single layered configuration contract for render/export behavior

The strongest conclusion is that `render` should become a first-class shared UI
feature owned by `src/app/ui/`, then exposed to GUI-like apps through adapters.

## Existing Shared Surface

### 1. Common UI entrypoint already exists

`src/app/ui/main.spl` already dispatches:
- `tui`
- `web`
- `tauri`
- `electron`
- `tui_web`
- `cli`
- `gui|desktop`
- `headless|none`

This is the user-facing command surface and the correct home for shared help and
mode semantics.

### 2. Clean parser attach point already exists

`src/app/ui/cli_entry.spl` is the narrow Rust-driver-facing parser. Its
`parse_ui_cli()` function is the cleanest place to auto-attach a new `render`
mode without copying parser logic into each app.

Current issue:
- `src/app/ui/main.spl` and `src/app/ui/cli_entry.spl` duplicate mode dispatch
- both will drift if `render` is added to only one path

### 3. Headless render primitives already exist

`src/app/ui.none/app.spl` and `src/app/ui.none/backend.spl` already provide:
- noninteractive headless execution
- render history
- `last_rendered_html`
- injected events for deterministic replay

This is the correct execution core for shared render/export, not app-local TUI
helpers.

### 4. Shared textual output primitives already exist

`src/app/ui.cli/observer.spl` already emits textual summaries and tree-oriented
views. That means shared `render` can support:
- `text`
- `tree`
- `html`

without inventing a new rendering core.

### 5. A shared render operation already exists at the tool layer

`src/app/ui.mcp/tools.spl` already includes `ui_render_file()`. This is the
best existing evidence that render belongs to a shared UI runtime rather than to
per-app flags.

## Existing GUI-Like Apps Outside Shared UI

### 1. `dashboard`

`src/app/dashboard/main.spl` owns its own CLI/GUI launch semantics. It reuses
backend detection ideas, but not the shared `simple ui` parser.

Risk:
- if `render` is added directly here, the repo gets another special-case flag

### 2. `llm_dashboard`

`src/app/llm_dashboard/main.spl` uses app-local `--tui` / `--gui` parsing and
directly routes between TUI and web GUI.

Risk:
- backend semantics drift from the shared UI stack

### 3. `office`

`src/app/office/mod.spl` is structurally UI-adjacent and currently prints load
summaries rather than using the shared UI render/export surface.

Recommendation:
- treat `dashboard`, `llm_dashboard`, and `office` as adapter clients of shared
  UI render, not owners of their own render flags

## Existing MDSOC Prior Art

### 1. Carets and configurable layering already exist

`src/compiler/85.mdsoc/config.spl` already parses:
- root carets
- dimension mappings
- `layer_order`
- `layer_direction`
- `allow_same_layer`
- `allow_adjacent_only`
- rule toggles such as `enforce_layering`

This means a render feature-caret can use existing MDSOC configuration
semantics. No new config language is required.

### 2. Manifest types already model carets and mappings

`src/compiler/85.mdsoc/types.spl` and `src/compiler/85.mdsoc/types/` already
define:
- `CaretId`
- `CaretMapping`
- `DimensionDef`
- `LayerDef`
- `MdsocManifest`

### 3. UI already has a proper layered precedent

`src/os/capsule.sdn` places:
- UI types in `types`
- compositor in a feature layer
- UI adaptation in `adapters`
- desktop apps in `apps`

This is strong local evidence that shared UI functionality should be modeled as
layered runtime plus adapter transforms, not as flat app flags.

### 4. Feature-through-layers precedent already exists

`src/compiler/85.mdsoc/feature/` already organizes behavior by feature
directory. `src/compiler/85.mdsoc/transform/` already models layer-to-layer
bridges such as parsing-to-desugaring and HIR-to-MIR.

Recommended reuse:
- treat `render` as a feature caret
- treat backend-specific preview/export paths as transforms

## Current Structural Problems

1. `--render` exists ad hoc in `examples/smux/main.spl`, not in shared UI.
2. Parser ownership is split between `src/app/ui/main.spl` and
   `src/app/ui/cli_entry.spl`.
3. Backend override is partly centralized in `src/app/ui/detect.spl`, but
   output/export config is not.
4. GUI-like apps still own launch/render semantics locally.
5. Demo content exists, but there is no defined default preview asset for
   system-level render verification.

## Recommended Local Architecture Direction

### Authoritative ownership

Put the shared render feature under `src/app/ui/`.

Do not add `--render` independently to:
- `dashboard`
- `llm_dashboard`
- `office`
- examples

### Parser ownership

Make `src/app/ui/cli_entry.spl` the parser authority for:
- `simple ui render`
- config attachment
- backend override attachment
- output format selection

Keep `src/app/ui/main.spl` as the broader script-compatible facade.

### Feature-caret structure

Use one feature id, for example `ui.render`, across multiple layers:
- parser layer
- config layer
- session layer
- render-core layer
- export layer
- adapter layer

That keeps one feature directory deployed through layers instead of scattering
render code by backend or app.

### Default demo asset

The best current default render target is:
- `examples/ui/widget_matrix.ui.sdn`

Reason:
- wide widget coverage
- stable for screenshots and HTML/text exports
- already useful as a system-level UI verification asset
