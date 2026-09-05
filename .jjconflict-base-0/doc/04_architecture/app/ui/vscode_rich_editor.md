<!-- codex-design -->
# Legacy VS Code Rich Editor Architecture

> Status note (2026-05-30): this document is legacy architecture for the
> standalone VS Code extension/webview path. It is not the source of truth for
> the Simple IDE/editor merge, embedded IDE app, example IDE, host/SimpleOS TUI
> path, or shared `src/lib/editor/` backend. For the current IDE architecture and
> runnable surfaces, see `doc/07_guide/ide_llm_integration_guide.md` and
> `doc/07_guide/editor_tui.md`.

**Feature:** legacy `vscode_rich_editor`; current feature is the shared Simple IDE/editor with a VS Code-compatible extension surface
**Date:** 2026-04-12  
**Status:** Provisional design based on recommended options  
**Assumption:** Feature Option 2 + NFR Option 2

## Architecture Decision

This legacy design built `vscode_rich_editor` as a standalone VS Code extension
package that used:

1. `CustomTextEditorProvider`
2. `TextDocument` as the canonical model
3. CodeMirror 6 in the webview as the rendered editor surface
4. range-based block synchronization between host and webview

## Major Components

### 1. Extension Shell

Owns:

- extension activation
- custom-editor registration
- command registration
- packaging/build layout

Legacy primary files were under `src/app/vscode_rich_editor/`; that package has
been removed. The current product entrypoint is `src/app/ide/main.spl`, with the
reusable editor backend under `src/lib/editor/`. The `examples/10_tooling/ide/**` files are
sample integrations only, not embedded app ownership.

### 2. Host Editor Provider

Owns:

- `resolveCustomTextEditor(...)`
- HTML/CSP assembly
- local resource root policy
- message routing
- application of text edits to the backing `TextDocument`

Current corresponding surfaces are `src/app/editor/gui_shell_core.spl`,
`src/app/editor/gui_shell_render.spl`, and the shared editor session model in
`src/lib/editor/core/session.spl`.

### 3. Block Analysis Capsule

Owns:

- detection of renderable blocks
- stable block identity
- content range extraction
- block metadata contract shared by host and webview

Current block analysis lives in `src/lib/editor/render/block_model.spl` and the
markdown-first render/services modules under `src/lib/editor/render/` and
`src/lib/editor/services/`.

### 4. Webview Editor Capsule

Owns:

- CodeMirror configuration
- widget insertion
- cursor-aware reveal/hide behavior
- local selection behavior
- posting edits and selection changes back to the host

Current GUI composition is `src/app/editor/gui_shell_render.spl`; host web,
browser, SDL, and Tauri presentation stays in adapter packages such as
`src/app/ui.web/`, `src/app/ui.browser/`, and `src/app/ui.tauri/`.

### 5. Renderers

Owns:

- math HTML generation
- image resolution
- placeholder/error visuals

Current renderer files are `src/lib/editor/70.backend/gui_backend.spl` for
portable editor HTML and `src/lib/editor/render/md_renderer.spl` for markdown
preview/TUI rendering.

## Required Architectural Corrections

### Stable block identity

Do not key rendered blocks by `prefix + content`.

Use one of:

1. `documentVersion + from + to + prefix`
2. host-assigned block ids carried across sync messages

### Block-local edits

The provider should move from whole-document replacement to targeted edits where
possible:

- replace only the active block range for block-local edits
- fall back to whole-document replace only when the entire editor buffer changed

### Shared block schema

Remove drift between:

- host block detection
- webview block detection

Target state:

- one shared block contract
- one shared parser or parser-generated metadata payload

## Hot Paths

### Startup path

1. extension activates
2. provider registers
3. VS Code opens `.spl` with custom editor
4. provider builds HTML
5. webview boots CodeMirror
6. host sends initial sync payload
7. webview installs widgets

### Hot request paths

- selection change
- block-local edit
- source document change from outside the rich editor
- image/math rerender

## Caching and Invalidation

### Keep

- rendered math HTML cache for repeated content
- webview context retention when hidden

### Add

- cache keys based on stable block identity, not content alone
- explicit invalidation on:
  - document version change
  - block range change
  - theme/resource reload if visuals depend on theme

## Performance Budget

- Warm activation under 150 ms
- Initial sync and first render under 200 ms for a representative file
- Selection sync under 25 ms
- Block-local edit echo under 60 ms

## Architecture Conclusion

The correct production path is to harden the existing standalone rich editor
package, not to keep layering richer behavior onto the legacy inline-decoration
extension.
