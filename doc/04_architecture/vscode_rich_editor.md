<!-- codex-design -->
# VS Code Rich Editor Architecture

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12  
**Status:** Provisional design based on recommended options  
**Assumption:** Feature Option 2 + NFR Option 2

## Architecture Decision

Build `vscode_rich_editor` as a standalone VS Code extension package that uses:

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

Primary files:

- [`src/app/vscode_rich_editor/package.json`](../../src/app/vscode_rich_editor/package.json)
- [`src/app/vscode_rich_editor/src/extension.ts`](../../src/app/vscode_rich_editor/src/extension.ts)

### 2. Host Editor Provider

Owns:

- `resolveCustomTextEditor(...)`
- HTML/CSP assembly
- local resource root policy
- message routing
- application of text edits to the backing `TextDocument`

Primary file:

- [`src/app/vscode_rich_editor/src/richCustomEditor.ts`](../../src/app/vscode_rich_editor/src/richCustomEditor.ts)

### 3. Block Analysis Capsule

Owns:

- detection of renderable blocks
- stable block identity
- content range extraction
- block metadata contract shared by host and webview

Primary baseline file:

- [`src/app/vscode_rich_editor/src/blockDetector.ts`](../../src/app/vscode_rich_editor/src/blockDetector.ts)

### 4. Webview Editor Capsule

Owns:

- CodeMirror configuration
- widget insertion
- cursor-aware reveal/hide behavior
- local selection behavior
- posting edits and selection changes back to the host

Primary files:

- [`src/app/vscode_rich_editor/src/webview/richEditorWebview.ts`](../../src/app/vscode_rich_editor/src/webview/richEditorWebview.ts)
- [`src/app/vscode_rich_editor/src/webview/decorationPlugin.ts`](../../src/app/vscode_rich_editor/src/webview/decorationPlugin.ts)

### 5. Renderers

Owns:

- math HTML generation
- image resolution
- placeholder/error visuals

Primary files:

- widget files under
  [`src/app/vscode_rich_editor/src/webview/widgets/`](../../src/app/vscode_rich_editor/src/webview/widgets)
- host-side image resolution in
  [`src/app/vscode_rich_editor/src/imageResolver.ts`](../../src/app/vscode_rich_editor/src/imageResolver.ts)

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
