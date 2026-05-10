<!-- codex-design -->
# VS Code Rich Editor Detail Design

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12  
**Status:** Provisional design based on recommended options

## Overview

The rich editor is a standalone VS Code extension that reopens `.spl` files in
a `CustomTextEditorProvider` and renders natural-height math and image widgets
inside a CodeMirror 6 webview.

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
