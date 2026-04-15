<!-- codex-design -->
# VS Code Extension Migration Plan

**Date:** 2026-04-12  
**Scope:** migrate old GUI/integration features into `src/app/vscode_extension` without destabilizing the rich custom editor

## Current Direction

Line-number alignment is deferred and ignored for the current migration tranche.

The next implementation priority is:

1. crash-contained host services
2. native diagnostics, warnings, errors, and symbol surfaces
3. tree-sitter-ready symbol/outline indexing
4. native test runner UI with running state
5. optional secondary panels after the native surfaces are stable

## Implementation Order

### Phase 1: Crash containment

- keep the rich custom editor working even if CLI, LSP, or WASM-adjacent services fail
- register each subsystem independently
- route failures to output/status/warnings instead of throwing during activation

### Phase 2: Native IDE surfaces

- fallback diagnostics in Problems
- fallback semantic tokens
- native document/workspace symbols
- native definition/hover entry points

These should live on VS Code-native surfaces, not inside the webview.

### Phase 3: Test runner GUI

- run icons/state via VS Code’s native test runner
- CodeLens for test blocks
- test workspace/artifact dialog as a secondary panel
- no CLI failure may crash the extension host or blank the editor

### Phase 4: Tree-sitter / Simple-WASM logic migration

- move symbol, diagnostic, test-model, and block-analysis logic toward shared Simple/WASM capsules
- keep TypeScript only for VS Code APIs, webview transport, and DOM/editor rendering

## Verification Gate

Every feature slice must pass:

1. `npm run compile` in `src/app/vscode_extension`
2. quit all Code windows
3. open a fresh isolated VS Code extension-development host
4. verify the rich editor still opens
5. verify the intended native UI surface works
6. inspect `main.log`, `renderer.log`, and extension-host output
7. human confirms no crash, blank webview, or broken GUI state

## Manual Fixtures

Use:

- `examples/phase1-math-blocks.spl` for custom-editor rendering stability
- `examples/phase2-ide-surfaces.spl` for symbols, diagnostics, and test UI

## Deferred Work

- line-number centering/alignment
- AI/chat migration
- old math preview/sync side panels
- full LSP client/server reintegration
