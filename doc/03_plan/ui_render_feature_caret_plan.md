# UI Render Feature Caret Plan

**Date:** 2026-04-03
**Status:** Proposed
**Research:** `doc/01_research/local/ui_render_feature_caret.md`,
`doc/01_research/domain/ui_render_feature_caret.md`

## Objective

Create one shared render/export capability for GUI-like surfaces, attach it to a
single configurable parser/config contract, and structure it as an MDSOC-style
feature caret that can be deployed through layers.

## Deliverables

1. Shared command surface:
   - `simple ui render <file.ui.sdn>`
2. Shared render config object with layered precedence
3. Adapter entrypoints for GUI-like apps
4. Default verification asset selection
5. Architecture and user guides

## Phase 1: Shared UI command

### Scope

- add `render` mode to `src/app/ui/cli_entry.spl`
- mirror dispatch/help in `src/app/ui/main.spl`
- implement on top of headless and observer primitives

### Acceptance

- no app-local parser required for `.ui.sdn` render/export
- `simple ui render examples/ui/widget_matrix.ui.sdn` works in Docker/headless
- output supports at least `text` and `html`

## Phase 2: Config layering

### Scope

Introduce one typed render config with fields such as:
- backend preference
- output format
- viewport/size
- demo/default asset
- adapter mode
- event replay selection

### Precedence

1. code defaults
2. feature config
3. environment
4. CLI flags

### Acceptance

- one parser authority populates the config
- help text reflects actual config knobs
- backend override and output override are documented and tested

## Phase 3: Feature-caret deployment through layers

### Scope

Represent render as one feature id deployed through explicit layers:
- parser
- config
- session
- render-core
- export
- adapters

Recommended implementation ownership under `src/app/ui/`.

### Acceptance

- each layer owns one responsibility
- backend code is adapter-only
- no backend directly owns shared render semantics

## Phase 4: GUI-like app adapters

### Scope

Migrate or wrap:
- `dashboard`
- `llm_dashboard`
- `office`

using the shared render/config contract.

### Acceptance

- GUI-like apps can reuse shared render/export behavior
- app-local `--render` implementations are removed or reduced to delegating
  shims

## Phase 5: Verification and docs

### Scope

- Docker/headless verification docs
- user guide for `simple ui render`
- architecture doc for feature-caret ownership
- regression tests around parser/help/config drift

### Acceptance

- documented default demo asset
- deterministic screenshots/text output for CI
- docs describe proper placement under `src/app/ui`

## Proposed File/Module Direction

### Runtime ownership

- `src/app/ui/cli_entry.spl`
- `src/app/ui/main.spl`
- `src/app/ui.none/*`
- `src/app/ui.cli/*`
- `src/app/ui.tui_web/*`

### Feature-caret layout direction

Recommended directory intent:

```text
src/app/ui/feature/render/
  parser/
  config/
  session/
  core/
  export/
  adapters/
```

This can start as module-group ownership before becoming a hard filesystem move.

## Risks

1. `dashboard` and `llm_dashboard` may need compatibility shims because they do
   not currently use `.ui.sdn` as their primary entrypoint.
2. Parser drift will continue if `cli_entry.spl` and `main.spl` are not unified.
3. A “render” command without a typed config object will become another
   flag-accumulation surface.
