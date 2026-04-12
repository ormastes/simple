<!-- codex-design -->
# Agent Tasks — VS Code Rich Editor

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12  
**Recommended Plan:** Robust Standalone Rich Editor

## Agent 1: Extension Shell and Packaging

Own:

- [`src/app/vscode_rich_editor/package.json`](../../../src/app/vscode_rich_editor/package.json)
- [`src/app/vscode_rich_editor/src/extension.ts`](../../../src/app/vscode_rich_editor/src/extension.ts)
- [`src/app/vscode_rich_editor/scripts/build-webview.mjs`](../../../src/app/vscode_rich_editor/scripts/build-webview.mjs)

Tasks:

- finalize extension metadata and activation events
- keep standalone build output self-contained
- add packaging and install/test scripts

## Agent 2: Host Custom Editor Provider

Own:

- [`src/app/vscode_rich_editor/src/richCustomEditor.ts`](../../../src/app/vscode_rich_editor/src/richCustomEditor.ts)

Tasks:

- replace whole-document edits with block-local edits where possible
- define the stable message contract
- harden sync and conflict handling
- keep CSP/resource loading restrictive

## Agent 3: Block Analysis and Identity

Own:

- [`src/app/vscode_rich_editor/src/blockDetector.ts`](../../../src/app/vscode_rich_editor/src/blockDetector.ts)
- shared block-contract code to be introduced

Tasks:

- introduce stable block ids
- remove duplicate-content collisions
- centralize host/webview block semantics

## Agent 4: Webview Editor and Widgets

Own:

- [`src/app/vscode_rich_editor/src/webview/richEditorWebview.ts`](../../../src/app/vscode_rich_editor/src/webview/richEditorWebview.ts)
- [`src/app/vscode_rich_editor/src/webview/decorationPlugin.ts`](../../../src/app/vscode_rich_editor/src/webview/decorationPlugin.ts)
- widget files under `src/webview/widgets/`

Tasks:

- preserve cursor-aware reveal behavior
- support natural-height math/image widgets
- keep search/history/selection behavior stable
- consume stable block ids from the host

## Agent 5: Tests and Verification

Own:

- standalone extension test harness to be created under `src/app/vscode_rich_editor/`

Tasks:

- add activation/open tests
- add duplicate-block rendering tests
- add block-local edit round-trip tests
- add missing-image and malformed-math fallback tests

## Implementation Order

1. block identity and message contract
2. block-local edit path
3. test harness and regression coverage
4. packaging polish and manual verification
