# UI Render Guide

## Purpose

This guide describes the intended shared render/export surface for UI assets and
GUI-like apps.

## Command

Primary shared surface:

```text
simple ui render <file.ui.sdn>
```

Recommended formats:
- `text`
- `tree`
- `html`

## Why Use Shared Render

Use shared render when you need:
- Docker/headless-safe UI inspection
- deterministic output for CI
- screenshot/text/HTML verification
- one common parser/config surface

Do not add a new app-local `--render` flag if shared UI can handle the request.

## Default Verification Asset

Default sample:

```text
examples/ui/widget_matrix.ui.sdn
```

Use it when:
- validating widgets
- checking theme/layout regressions
- generating a known-good render artifact

## Ownership Rules

Shared runtime ownership:
- `src/app/ui/`

App-specific adapters:
- `src/app/dashboard/`
- `src/app/llm_dashboard/`
- `src/app/office/`

Rule:
- apps may adapt into shared render
- apps should not redefine shared render semantics

## Config Model

Render behavior should be configured by one shared config object with layered
precedence:

1. defaults
2. feature config
3. environment
4. CLI

Backend selection should participate in that same model.

## Docker/Headless Use

Shared render should work without raw terminal mode or desktop startup. Prefer
it for:
- CI snapshots
- text inspection
- HTML capture
- container verification

Current practical Docker verification paths in this repo are:
- `simple-test-isolation:codex-current` for noninteractive example and probe runs
- `simple-tauri-gui:latest` for real desktop-window capture via Xvfb/VNC

Examples verified on 2026-04-03:
- `examples/ui/launch_verified.spl`
- `examples/ui/launch_tui_verified.spl`
- `examples/ui/runtime_probe.spl`
- `examples/ui/smoke_test.spl`

The Tauri container also produced a real GUI screenshot from
`examples/ui/test_render.spl` after rebuilding the shell from current mounted
sources.

Known limitation from that pass:
- `examples/ui/hello_tui.spl` still times out in Docker and needs separate
  runtime investigation

## Migration Guidance

If an app already has local preview/render flags:

1. keep a temporary compatibility shim
2. delegate implementation into shared UI render
3. remove app-local semantics once migration is complete

## Notes From The 2026-04-03 Verification Pass

- `examples/ui/launch_verified.spl` required a fix from `UITree(root_id: ...)`
  to `UITree.new(root)`.
- the Tauri shell required the same `got_render` guard in `lib.rs` that already
  existed in the duplicate `app.rs` path, otherwise the fallback status page
  overwrote valid rendered HTML after stdout closed.
