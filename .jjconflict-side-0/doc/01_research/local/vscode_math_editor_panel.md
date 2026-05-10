<!-- codex-research -->
# VS Code Math Editor Panel Research

**Date:** 2026-04-10  
**Feature:** `vscode_math_editor_panel`

## Executive Summary

The current VS Code math UX is split across:

- source-editor decoration rendering in [`src/app/vscode_extension/src/math/mathDecorationProvider.ts`](../../../src/app/vscode_extension/src/math/mathDecorationProvider.ts)
- hover rendering in [`src/app/vscode_extension/src/math/mathHoverProvider.ts`](../../../src/app/vscode_extension/src/math/mathHoverProvider.ts)
- a preview webview in [`src/app/vscode_extension/src/math/mathPreviewPanel.ts`](../../../src/app/vscode_extension/src/math/mathPreviewPanel.ts)

The source editor already supports inline conceal/reveal, cursor-aware raw-source fallback, hover, and config-driven alignment/debug controls. The preview panel already supports rendered math in a webview. What is missing is a single panel that behaves like the source editor surface without losing edit/search/undo/diagnostic integration.

## 1. Current Source-Editor Behavior

### Already supported

- Inline math block detection for `m{}`, `loss{}`, `nograd{}` in [`mathDecorationProvider.ts`](../../../src/app/vscode_extension/src/math/mathDecorationProvider.ts)
- Cursor-aware reveal when the caret is on the math line
- SVG rendering via MathJax + disk cache
- Unicode fallback when SVG is unavailable
- Hover rendering with structured math summaries in [`mathHoverProvider.ts`](../../../src/app/vscode_extension/src/math/mathHoverProvider.ts)
- WASM-backed math-core bridge fallback in [`mathCoreWasm.ts`](../../../src/app/vscode_extension/src/math/mathCoreWasm.ts)
- Commands/config toggles in [`package.json`](../../../src/app/vscode_extension/package.json) and [`src/app/vscode_extension/src/math/index.ts`](../../../src/app/vscode_extension/src/math/index.ts)

### Current limitation

- The source editor is still the canonical editor surface.
- There is no custom editor provider in the extension.
- Decoration attachments can influence the attachment box, but they do not provide true per-line editor line-height control.

## 2. Existing Panel/Webview Baseline

### `MathPreviewPanel`

[`mathPreviewPanel.ts`](../../../src/app/vscode_extension/src/math/mathPreviewPanel.ts) is the closest existing “math panel”:

- `createWebviewPanel(...)`
- offline-safe HTML
- KaTeX rendering
- local resource loading and CSP
- cursor-driven updates from the active source editor
- rendered output plus source block display

It is read-only. It does not implement document editing, undo/redo, search, or save semantics.

### Other reusable webview patterns

- [`src/app/vscode_extension/src/ai/chatPanel.ts`](../../../src/app/vscode_extension/src/ai/chatPanel.ts) shows a two-way `postMessage` pattern with state held in the extension host.
- [`src/app/ui.vscode/backend.spl`](../../../src/app/ui.vscode/backend.spl) and [`src/app/ui.vscode/protocol.spl`](../../../src/app/ui.vscode/protocol.spl) show the repo’s general webview message and HTML/CSP patterns.

## 3. What A Real Source-Editor-Like Panel Must Add

To match source-editor behavior, a new panel must support:

- cursor tracking
- text selection sync
- edits that update the underlying text model
- undo/redo
- search/find
- diagnostics refresh
- hover
- code actions
- save/revert/debounce

If it is only a preview panel, it cannot be the authoritative editor and will not naturally support those behaviors.

## 4. Local Research Conclusion

The repo already has enough code to build a synchronized math panel, but not a real custom editor yet.

The lowest-risk path is:

1. keep the source editor authoritative
2. keep the preview panel as the rendered companion
3. add synchronized edit/cursor state if we need a richer panel

## 5. File References

- [`mathDecorationProvider.ts`](../../../src/app/vscode_extension/src/math/mathDecorationProvider.ts)
- [`mathHoverProvider.ts`](../../../src/app/vscode_extension/src/math/mathHoverProvider.ts)
- [`mathPreviewPanel.ts`](../../../src/app/vscode_extension/src/math/mathPreviewPanel.ts)
- [`mathCoreWasm.ts`](../../../src/app/vscode_extension/src/math/mathCoreWasm.ts)
- [`math/index.ts`](../../../src/app/vscode_extension/src/math/index.ts)
- [`package.json`](../../../src/app/vscode_extension/package.json)
