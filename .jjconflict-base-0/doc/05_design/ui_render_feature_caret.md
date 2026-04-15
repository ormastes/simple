# UI Render Feature Caret Design

## Design Goal

Define a practical design for rolling out `render` as a shared feature before a
full tree refactor.

## Public Command Shape

Primary command:

```text
simple ui render <file.ui.sdn>
```

Suggested configurable flags:
- `--format=text|tree|html`
- `--backend=auto|headless|tui|web|tauri|electron`
- `--width=<n>`
- `--height=<n>`
- `--theme=<name>`
- `--demo=<path-or-default>`

The parser should populate one typed config object. It should not directly wire
flags into multiple backend paths.

## Default Demo Behavior

If a user needs a known-good sample asset, the default should be:

```text
examples/ui/widget_matrix.ui.sdn
```

Reason:
- broad widget coverage
- useful for screenshots
- useful for HTML/text export verification

## Compatibility Design For Non-`.ui.sdn` Apps

### `dashboard`

Expose a render adapter that produces either:
- a `.ui.sdn` export surface
- or a renderable shared UI model

### `llm_dashboard`

Expose a compatibility adapter instead of maintaining separate `--tui`/`--gui`
only semantics for preview/export.

### `office`

Move from print-only summaries toward shared render/export once the common
contract exists.

## Suggested Internal Types

### `RenderConfig`

Fields:
- `mode`
- `backend`
- `format`
- `width`
- `height`
- `theme`
- `asset_path`
- `adapter_name`
- `use_default_demo`

### `RenderRequest`

Fields:
- `config`
- `session_factory`
- `export_targets`

### `RenderResult`

Fields:
- `format`
- `text`
- `html`
- `metadata`
- `warnings`

## Layered Feature-Caret Mapping

Suggested logical caret:
- `ui.render`

Suggested layer mapping:

| Layer | Responsibility | Suggested modules |
|---|---|---|
| parser | parse CLI and config binding | `app/ui/cli_entry.spl`, `app/ui/main.spl` |
| config | typed config and precedence | new shared config module under `app/ui` |
| session | state/session creation | `app/ui.none/app.spl` |
| core | render execution | `app/ui.none/backend.spl` |
| export | text/tree/html export | `app/ui.cli/*`, `app/ui.tui_web/*` |
| adapters | app/backend bridges | `dashboard`, `llm_dashboard`, `office` |

## Testing Direction

### Parser tests

Validate:
- `render` mode parsing
- config precedence
- invalid combinations rejected

### Runtime tests

Validate:
- deterministic render result for default asset
- `text` and `html` output
- Docker/headless execution

### Adapter tests

Validate:
- app adapters delegate to shared render
- no incompatible output semantics

## Non-Goals

- Do not make every app own a complete custom render pipeline.
- Do not bind render behavior directly to a single GUI backend.
- Do not require a full MDSOC tree rewrite before the shared command ships.
