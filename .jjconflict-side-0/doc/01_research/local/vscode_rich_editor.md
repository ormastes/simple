<!-- codex-research -->
# VS Code Rich Editor Local Research

**Date:** 2026-04-12  
**Feature:** `vscode_rich_editor`

## Executive Summary

The repo already contains a standalone VS Code extension package at
[`src/app/vscode_rich_editor/`](../../../src/app/vscode_rich_editor) that is
explicitly targeting a custom editor with natural variable-height rendering.
This is a stronger starting point than the older `vscode_math_editor_panel`
companion-panel work because it already uses a standalone
`CustomTextEditorProvider` plus a CodeMirror 6 webview editor.

## Current Package Shape

### Extension shell

- [`src/app/vscode_rich_editor/package.json`](../../../src/app/vscode_rich_editor/package.json)
  registers a standalone extension named `simple-rich-editor`
- it contributes a custom editor with `viewType = simple.richSourceEditor`
- activation is currently language-based (`onLanguage:simple`)
- build output is local to the package (`out/`)

### Host-side custom editor

- [`src/app/vscode_rich_editor/src/extension.ts`](../../../src/app/vscode_rich_editor/src/extension.ts)
  registers `RichCustomEditorProvider`
- it uses `retainContextWhenHidden: true`
- it disables multi-editor-per-document with `supportsMultipleEditorsPerDocument: false`
- it exposes a command to reopen the current file in the rich editor

### Document and rendering host logic

- [`src/app/vscode_rich_editor/src/richCustomEditor.ts`](../../../src/app/vscode_rich_editor/src/richCustomEditor.ts)
  owns:
  - `resolveCustomTextEditor(...)`
  - HTML/CSP generation
  - webview message handling
  - full-document sync and edit application
  - host-side KaTeX/image rendering payload generation
- host edits currently replace the full document using `WorkspaceEdit.replace(...)`
  rather than applying minimal block-local edits

### Block parsing

- [`src/app/vscode_rich_editor/src/blockDetector.ts`](../../../src/app/vscode_rich_editor/src/blockDetector.ts)
  detects `m{}`, `loss{}`, `nograd{}`, `img{}`, and `graph{}`
- parsing is regex-based and supports only one level of nested braces
- the same regex logic is duplicated in the webview decoration plugin:
  [`src/app/vscode_rich_editor/src/webview/decorationPlugin.ts`](../../../src/app/vscode_rich_editor/src/webview/decorationPlugin.ts)

### Webview editor

- [`src/app/vscode_rich_editor/src/webview/richEditorWebview.ts`](../../../src/app/vscode_rich_editor/src/webview/richEditorWebview.ts)
  embeds CodeMirror 6 and already includes:
  - history
  - search keymap
  - bracket matching
  - syntax highlighting
  - line numbers
  - selection mirroring
  - debounced full-text edits back to the host
- widget rendering is delegated to:
  - [`mathWidget.ts`](../../../src/app/vscode_rich_editor/src/webview/widgets/mathWidget.ts)
  - [`imageWidget.ts`](../../../src/app/vscode_rich_editor/src/webview/widgets/imageWidget.ts)
  - [`placeholderWidget.ts`](../../../src/app/vscode_rich_editor/src/webview/widgets/placeholderWidget.ts)

## Important Implementation Findings

### 1. The extension already matches the requested direction

The current package is not a preview panel. It is already a whole new VS Code
extension package with a custom text editor and natural-height widgets.

### 2. Full-document edit replacement is the main correctness risk

The webview sends `editAll`, and the host replaces the entire document text.
That is simple but increases risk for:

- undo granularity
- jitter for larger files
- selection drift after concurrent edits
- conflict handling if external edits land between syncs

### 3. Rendered-block identity is unstable for duplicate content

The webview caches rendered blocks by:

- ``${block.prefix}:${block.content}``

This collides when two blocks share the same prefix and source text.
Examples:

- two identical `m{ x + y }` blocks
- repeated `img{ diagram.png }` blocks

The next design phase should use stable range-based or id-based block identity.

### 4. Parser duplication exists across host and webview

The repo currently duplicates regex block detection on both sides of the
message boundary. That is acceptable for prototyping, but it is not the right
long-term architecture because block semantics can drift.

### 5. The package lacks its own formal docs and tests

There are no package-local docs or test files under
`src/app/vscode_rich_editor/`. The only formal planning artifacts today are for
the older panel-based approach under:

- [`doc/01_research/local/vscode_math_editor_panel.md`](../local/vscode_math_editor_panel.md)
- [`doc/05_design/vscode_math_editor_panel.md`](../../05_design/vscode_math_editor_panel.md)

## Local Research Conclusion

`vscode_rich_editor` is the correct baseline for the requested feature:

1. whole new extension package
2. real `CustomTextEditorProvider`
3. CodeMirror 6 webview
4. natural variable-height math/image widgets

The implementation should proceed by hardening this package rather than trying
to keep extending the old inline-decoration extension path.
