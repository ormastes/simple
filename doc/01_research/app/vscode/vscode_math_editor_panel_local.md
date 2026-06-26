<!-- codex-research -->
# VS Code Math Editor Panel Domain Research

**Date:** 2026-04-10  
**Feature:** `vscode_math_editor_panel`

## Official VS Code Findings

### Webviews are HTML/CSS surfaces

VS Code’s webview API documents a normal HTML document, injected CSS, and `webview.postMessage(...)` / `acquireVsCodeApi()` message passing. That means a webview can control its own layout, including line height, because it is not the source editor.

Source:
- [VS Code Webview API](https://code.visualstudio.com/api/extension-guides/webview)

### Custom text editors are document-backed

The custom editor API says text-based custom editors use the normal `TextDocument` as their document model. They can support editing, undo/redo, save, hot exit, and multi-editor synchronization, but the extension must implement the document lifecycle and edit plumbing.

Source:
- [VS Code Custom Editor API](https://code.visualstudio.com/api/extension-guides/custom-editors)

### Markdown preview styling is CSS-based

The Markdown extension guide shows that preview styling is handled with preview CSS and webview resources, not by changing the source editor line-height.

Source:
- [VS Code Markdown Extension Guide](https://code.visualstudio.com/api/extension-guides/markdown-extension)

### Variable editor line heights are not exposed to extensions

VS Code release notes mention variable line heights in Monaco, but that capability is not available to extensions yet.

Source:
- [VS Code 1.100 Release Notes](https://code.visualstudio.com/updates/v1_100)

## What This Means For Math

- If the goal is true visual spacing control, a webview can do it.
- If the goal is source-editor parity, a custom text editor can do it only by reimplementing document editing semantics.
- If the goal is “keep the text editor as source of truth and add a richer rendered panel,” a synchronized webview is the practical compromise.

## Practical Recommendation From Domain Research

For math embedded in `.spl` source, a custom text editor is usually heavier than needed.

The strongest fit is:

1. use the existing text editor as the canonical source surface
2. add a synced webview/panel for richer rendering and interaction
3. reserve a custom text editor for a future dedicated math file type

## External References

- [Webview API](https://code.visualstudio.com/api/extension-guides/webview)
- [Custom Editor API](https://code.visualstudio.com/api/extension-guides/custom-editors)
- [Markdown Extension Guide](https://code.visualstudio.com/api/extension-guides/markdown-extension)
- [VS Code 1.100 Release Notes](https://code.visualstudio.com/updates/v1_100)
