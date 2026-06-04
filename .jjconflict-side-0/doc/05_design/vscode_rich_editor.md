<!-- codex-design -->
# Legacy VS Code Rich Editor Detail Design

> Status note (2026-05-30): this document is legacy detail design for the
> standalone VS Code extension/webview path. It does not describe the current
> Simple IDE/editor merge or the host/SimpleOS-safe shared editor library.
> Current source-of-truth docs are `doc/07_guide/ide_llm_integration_guide.md`
> and `doc/07_guide/editor_tui.md`.

**Feature:** legacy `vscode_rich_editor`; current feature is the shared Simple IDE/editor with a VS Code-compatible extension surface
**Date:** 2026-04-12  
**Status:** Provisional design based on recommended options

## Overview

The original rich editor design targeted a standalone VS Code extension that
reopened `.spl` files in a `CustomTextEditorProvider` and rendered
natural-height math and image widgets inside a CodeMirror 6 webview. That
standalone implementation tree has been removed; current work routes through
the shared Simple editor/IDE surfaces in `src/lib/editor/`, `src/app/editor/`,
and `src/app/ide/main.spl`. The `examples/ide/**` files are sample integrations
that demonstrate launch and render contracts; they are not the embedded app.

Current work is Markdown-first: Markdown notes, wiki links, preview, outline,
tasks, tables, callouts, and attachments are first-class editor workflows.
`.spl` remains a supported language mode over the same shared buffer/session
model.

The backing `TextDocument` remains canonical.

## Message Contract

### Webview -> Host

- `ready`
- `selectionChanged`
- `editBlock`
- `editAll`
- `requestSync`

## Host -> Webview

- `sync`
- `applySelection`
- `error`

## Block Model

Each renderable block should carry:

- `id`
- `kind`
- `from`
- `to`
- `prefix`
- `content`
- `displayMode`
- `status`
- `renderedHtml`
- `imageUri`
- `errorMessage`

### Identity Rule

`id` must not be derived only from content. Use a stable range-based identity
for the current document version.

## Edit Flows

### Block-local edit

1. user edits inside a revealed raw block in CodeMirror
2. webview posts `editBlock` with `blockId`, `from`, `to`, and replacement text
3. host validates the current block identity against the latest document
4. host applies a targeted `WorkspaceEdit`
5. host emits a new `sync` payload

### Full-buffer edit fallback

Use `editAll` only for:

- structural edits outside tracked block boundaries
- parser-desync recovery
- initial implementation fallback paths

## Selection Sync

### Webview -> Host

- send anchor/head offsets
- include active block id when available

### Host -> Webview

- clamp selection to current document length
- if the block changed due to external edits, remap to the nearest surviving
  range before reapplying selection

## Rendering Rules

### Math

- render KaTeX HTML at natural DOM height
- preserve raw source when the cursor is inside the block
- show placeholder/error widget on render failure

### Images

- resolve resource URIs through the webview resource pipeline
- render block-level images at natural height with max-width constraints
- show explicit error widgets for missing files

## Parser Strategy

### MVP

- keep regex-based block detection
- centralize it so the webview does not maintain a second divergent regex

### Follow-up

- move to parser/WASM-produced block metadata once the contract stabilizes

## Observability

Add debug logging or timing hooks for:

- initial sync time
- block render time
- edit apply latency
- resync count
- recovery path entry count

## Major Risks

### Duplicate block collisions

Resolved by explicit block ids.

### Whole-document rewrite churn

Resolved by preferring block-local edits.

### Parser drift between host and webview

Resolved by centralizing the block contract.
