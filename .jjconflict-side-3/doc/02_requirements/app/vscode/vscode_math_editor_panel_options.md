<!-- codex-research -->
# VS Code Math Editor Panel Requirements Options

**Feature:** `vscode_math_editor_panel`  
**Date:** 2026-04-10

## Goal

Provide a math panel that supports source-editor-like behavior without losing the current editor workflow.

## Option 1: Preview-First Companion Panel

**Description**
- Keep the current source editor authoritative.
- Expand the existing preview webview into a richer rendered companion panel.
- Use cursor/selection to mirror the active math block, but keep edits in the source editor.

**Pros**
- Lowest implementation risk
- Reuses [`mathPreviewPanel.ts`](../../../src/app/vscode_extension/src/math/mathPreviewPanel.ts) and the existing source-editor pipeline
- Fastest to ship
- No custom document model required

**Cons**
- Not a real editor surface
- Cannot own undo/redo, search, or save semantics
- Editing still happens in the source editor

**Effort**
- `S`
- Roughly 1-2 source files plus tests

## Option 2: Synced Source-Editor Companion Panel

**Description**
- Keep the source editor canonical.
- Add a synchronized panel that mirrors cursor/selection, renders math, and drives edits back into the real `TextDocument`.
- Use the source editor as the actual edit buffer and the panel as a richer rendering/control surface.

**Pros**
- Best fit for “support all source-editor features”
- Preserves the existing VS Code language-service and document pipeline
- Can reuse current math rendering and hover logic
- Does not require inventing a new file format

**Cons**
- More moving parts than Option 1
- Requires careful sync between panel state and the text document
- Still not a true standalone editor buffer

**Effort**
- `M`
- Roughly 4-6 source files plus tests

## Option 3: Custom Text Editor / Dedicated Math Editor

**Description**
- Implement a real custom editor or custom text editor for a math-specific surface.
- Treat the rendered math panel as the primary editor experience.
- Reimplement text-document lifecycle, edits, undo/redo, save/revert, and multi-editor sync.

**Pros**
- Strongest source-editor-like UX inside the panel itself
- Best if this becomes a dedicated math authoring surface
- Can own layout and interaction completely

**Cons**
- Highest complexity
- Highest maintenance cost
- Larger risk of duplicating the source editor and language-service pipeline

**Effort**
- `L`
- Roughly 8-12 source files plus tests and lifecycle plumbing

## Recommended Choice

Choose **Option 2**.

It is the best balance between:

- preserving all source-editor behavior in practice
- keeping the source editor canonical
- avoiding a full custom editor framework
- getting a richer math panel without overbuilding

## Feature/Behavior Fit

| Capability | Option 1 | Option 2 | Option 3 |
|---|---:|---:|---:|
| Cursor sync | P | Y | Y |
| Selection sync | P | Y | Y |
| Edits in panel | N | Y* | Y |
| Undo/redo | N | Y* | Y |
| Search | N | Y* | Y |
| Diagnostics | Y* | Y* | Y |
| Code actions | Y* | Y* | Y |
| Hover | Y* | Y* | Y |
| Inline rendering | Y | Y | Y |
| Save/revert | N | Y* | Y |

`Y*` means supported through the paired source document pipeline rather than as a standalone panel buffer.

