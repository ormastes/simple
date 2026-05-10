<!-- codex-design -->
# Agent Tasks — VS Code Math Editor Panel

**Feature:** `vscode_math_editor_panel`  
**Date:** 2026-04-10  
**Recommended Plan:** Synced Source-Editor Companion Panel

## Chosen Plan

Use the existing source editor as the canonical edit surface and add a synchronized math panel/webview that mirrors cursor, selection, and rendered math. Do not replace the source editor with a custom editor unless a dedicated math file type becomes a real requirement.

## Why This Plan

- Preserves all source-editor behavior
- Reuses the current math rendering stack
- Avoids the cost of implementing a full custom text editor lifecycle
- Fits the repo’s existing webview/message patterns

## Agent Breakdown

### Agent 1: Panel Shell and Webview Sync

Own:
- [`src/app/vscode_extension/src/math/mathPreviewPanel.ts`](../../../src/app/vscode_extension/src/math/mathPreviewPanel.ts)
- [`src/app/vscode_extension/src/ai/chatPanel.ts`](../../../src/app/vscode_extension/src/ai/chatPanel.ts)

Tasks:
- add a synchronized panel mode
- keep source document as the canonical model
- mirror active block, cursor, and selection
- add message schema for panel events
- keep offline-safe CSP/resource loading

### Agent 2: Document and Editor Integration

Own:
- [`src/app/vscode_extension/src/math/mathDecorationProvider.ts`](../../../src/app/vscode_extension/src/math/mathDecorationProvider.ts)
- [`src/app/vscode_extension/src/math/mathHoverProvider.ts`](../../../src/app/vscode_extension/src/math/mathHoverProvider.ts)
- [`src/app/vscode_extension/src/math/index.ts`](../../../src/app/vscode_extension/src/math/index.ts)

Tasks:
- preserve inline conceal/reveal behavior
- keep hover and diagnostics pipeline intact
- map panel selection back to source block ranges
- maintain config toggles and debug layout logging

### Agent 3: Rendering and Layout

Own:
- [`src/app/vscode_extension/src/math/mathConverter.ts`](../../../src/app/vscode_extension/src/math/mathConverter.ts)
- [`src/app/vscode_extension/src/math/mathSvgRenderer.ts`](../../../src/app/vscode_extension/src/math/mathSvgRenderer.ts)

Tasks:
- keep LaTeX/unicode conversion authoritative
- keep SVG preview generation and caching
- ensure panel rendering matches source-editor math output
- preserve the current height/spacing heuristics

### Agent 4: Tests and Verification

Own:
- [`src/app/vscode_extension/src/test/gui/mathRendering.test.ts`](../../../src/app/vscode_extension/src/test/gui/mathRendering.test.ts)
- math demo files under [`src/app/vscode_extension/test-workspace/`](../../../src/app/vscode_extension/test-workspace/)

Tasks:
- add panel interaction tests
- verify cursor/selection mirroring
- verify hover and diagnostics still work from the source editor
- verify source edits flow through to the panel
- keep the math arithmetic and DL demo workspaces as visual smoke fixtures

## Implementation Order

1. Panel shell and state sync
2. Source-document integration
3. Rendering parity
4. Test coverage and regression checks

## Exit Criteria

- source editor still works exactly as today
- panel mirrors the active math block and selection
- hover/diagnostics/code actions still operate on the source document
- edits made in the panel flow back to the source document
- math rendering stays offline-safe and cache-backed

