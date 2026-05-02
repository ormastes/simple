<!-- codex-research -->
# VS Code Rich Editor Domain Research

**Date:** 2026-04-12  
**Feature:** `vscode_rich_editor`

## Official Findings

### Custom text editors are the right VS Code primitive for text-backed rich editors

The official VS Code custom editor guide states that custom editors are
webview-based alternative views, and that `CustomTextEditorProvider` uses the
standard `TextDocument` model for text files. That keeps save, hot-exit, and
text editing behavior on the VS Code side instead of forcing the extension to
invent a new document model.

Source:
- https://code.visualstudio.com/api/extension-guides/custom-editors

### Webviews are the supported UI surface for custom editors

The official webview guide confirms the expected architecture:

- extension host sends JSON-serializable messages with `webview.postMessage(...)`
- the webview receives them with `window.addEventListener('message', ...)`
- the webview replies using `acquireVsCodeApi().postMessage(...)`
- local resource loading must be restricted with `localResourceRoots`

Source:
- https://code.visualstudio.com/api/extension-guides/webview

### April 2025 changed the Monaco background, but not the recommended extension plan

VS Code 1.100 release notes from April 2025 introduced Monaco-side variable
line heights via `IModelDecorationOptions`, but the release notes also say this
work was not yet available to extensions at rollout time. That matters because
it removes the old assumption that Monaco can never do this internally, but it
does **not** remove the need for a custom-editor strategy for a published
extension today.

Source:
- https://code.visualstudio.com/updates/v1_100

### CodeMirror 6 directly supports the rendering model this feature needs

The official CodeMirror decoration example documents:

- widget decorations
- replacing decorations
- line decorations
- block widgets

and explicitly calls out that decorations which change vertical layout, such as
block widgets, must be provided directly. That aligns closely with this repo’s
current webview implementation strategy.

Source:
- https://codemirror.net/examples/decoration/

## What This Means For The Feature

### Recommended editor model

Use:

1. `CustomTextEditorProvider`
2. a webview-hosted CodeMirror 6 editor
3. the real VS Code `TextDocument` as the source of truth

Do **not** use:

- `CustomEditorProvider` with a custom document model for `.spl`
- a preview-only panel pretending to be the editor
- direct dependency on future Monaco line-height APIs for MVP delivery

### Why the custom-editor path still wins

Even if Monaco line-height APIs eventually become stable for extensions, this
feature still needs more than taller lines:

- rendered math blocks
- rendered images
- replacement widgets
- block-level interaction
- richer editor-local layout than native text decorations offer

Those needs are already a natural fit for a webview editor.

## Domain Research Conclusion

The best architecture for a new Simple rich editor extension is still:

1. standalone VS Code extension package
2. `CustomTextEditorProvider`
3. CodeMirror 6 in the webview
4. range-based synchronization back to `TextDocument`

This remains the lowest-risk path even after the April 2025 Monaco update.
