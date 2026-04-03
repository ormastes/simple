# UI Render Feature Caret Architecture

## Purpose

This document defines the target architecture for making render/export a shared
UI runtime feature rather than an app-local CLI flag.

The design follows existing repo direction:
- shared UI ownership under `src/app/ui/`
- MDSOC carets and configurable dimensions from `src/compiler/85.mdsoc/`
- layered UI placement precedent from `src/os/capsule.sdn`

## Problem

Current render and GUI launch semantics are split across:
- shared UI entrypoints
- app-local launchers
- example-local flags such as `smux --render`

This creates three kinds of drift:
1. parser drift
2. config drift
3. output/preview drift

## Architectural Decision

### Decision 1: Shared ownership

All common render/export behavior belongs to `src/app/ui/`.

Per-app code may:
- provide assets
- provide adapter-specific view models
- provide compatibility shims

Per-app code must not:
- become the parser authority for shared render behavior
- define incompatible output semantics
- define new standalone render flags when delegation is possible

### Decision 2: Feature-caret model

Represent render as one feature caret, for example `ui.render`.

This feature is deployed through explicit layers:
- parser
- config
- session
- render-core
- export
- adapters

The same feature id stays stable while responsibility moves downward through
layers.

### Decision 3: Adapter backends

Backends are adapters over shared render data.

Examples:
- `tui`
- `web`
- `tauri`
- `electron`
- `headless`

Backends may choose how to display or transport render output, but they do not
own the meaning of:
- `render`
- output format
- default preview asset
- config precedence

### Decision 4: Single parser authority

`src/app/ui/cli_entry.spl` is the parser authority for `simple ui`.

`src/app/ui/main.spl` remains the broader script-compatible facade, but mode and
flag semantics should flow from the same authoritative parse contract.

## Layer Model

## Parser Layer

Responsibilities:
- parse command mode
- attach config fields
- validate allowed combinations

Candidate ownership:
- `src/app/ui/cli_entry.spl`

## Config Layer

Responsibilities:
- typed render config object
- precedence rules
- defaults and validation

Suggested fields:
- `backend`
- `format`
- `width`
- `height`
- `theme`
- `default_asset`
- `adapter`
- `event_profile`

## Session Layer

Responsibilities:
- UI session creation
- event replay
- state capture

Existing base:
- `src/app/ui.none/app.spl`

## Render-Core Layer

Responsibilities:
- noninteractive render execution
- state-to-output transformation
- stable capture APIs

Existing base:
- `src/app/ui.none/backend.spl`
- shared UI tree/session primitives

## Export Layer

Responsibilities:
- text export
- tree export
- HTML export
- screenshot-ready artifact generation later

Existing base:
- `src/app/ui.cli/observer.spl`
- `src/app/ui.tui_web/screen_to_html.spl`

## Adapter Layer

Responsibilities:
- backend-specific transport and launch
- app-specific compatibility wrappers

Examples:
- `dashboard`
- `llm_dashboard`
- `office`

## Configurability Model

Each layer-related value should be configurable through one shared config
contract.

Recommended precedence:
1. built-in defaults
2. feature config file or module defaults
3. environment variables
4. CLI flags

The existing `SIMPLE_GUI_BACKEND` environment variable becomes one input to the
shared config model, not a parallel standalone system.

## Proper UI Placement

Shared UI runtime logic belongs under:
- `src/app/ui/`

App-specific UI business logic belongs under its app tree:
- `src/app/dashboard/`
- `src/app/llm_dashboard/`
- `src/app/office/`

Cross-cutting render/export behavior should not live in those app trees.

## MDSOC Alignment

This design fits the existing MDSOC model because:
- carets already exist
- layer orders and layer rules are already configurable
- transform-style bridges already exist elsewhere in the repo
- UI already has a layered precedent in `src/os/capsule.sdn`

## Migration Rules

1. No new app-local `--render` flags unless they delegate into shared UI.
2. New GUI-like apps must register a render adapter instead of inventing a new
   parser.
3. Default verification should use a shared demo asset.
4. Shared docs and tests must validate help/config/output parity.
