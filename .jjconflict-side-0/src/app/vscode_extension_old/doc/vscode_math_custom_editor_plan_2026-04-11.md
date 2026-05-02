# VS Code Math Custom Editor Plan

## Scope

Stabilize and complete the VS Code math editing experience around a real `CustomTextEditor` for `.spl` files with math blocks. The current custom editor shell exists, but only the first phase is complete.

This file is placed in `doc/plan/` because that was explicitly requested, even though the directory is marked legacy.

## Current State

- A custom editor is registered for `.spl` files as `simple.mathSourceEditor`.
- The custom editor opens a document, shows the full source in a textarea, and renders the active math block beside it.
- Webview CSP for KaTeX assets is already corrected to use `webview.cspSource`.
- The math-related GUI test suite passes in the VS Code renderer log.
- The full GUI suite is still blocked by unrelated AI command failures in the extension test harness.

## Goal

Finish the custom math editor in controlled phases:

1. keep the source document canonical
2. make rendering stable and non-crashing
3. add editor behaviors one by one
4. migrate math logic toward Simple/WASM once the host/webview contract is stable

## Constraints

- Do not regress the existing source editor path.
- Do not depend on inline decoration hacks for editor-height behavior.
- Invalid math must render a fallback state, not crash the editor.
- VS Code host integration remains in TypeScript until the WASM contract is mature.

## Phase Plan

### Phase 1: Shell Stabilization

Status: done

- register `CustomTextEditorProvider`
- open `.spl` with the custom view
- sync full-document source into the webview
- apply source edits back to the backing `TextDocument`
- prevent basic selection-sync loops

Exit criteria:

- custom editor opens reliably
- edits round-trip to the backing file
- external document changes resync into the webview

### Phase 2: Rendering Stabilization

Status: in progress

- keep active math-block detection local to the current caret offset
- render the active block with KaTeX in the custom editor
- show fallback content for malformed math
- verify no CSP/resource regressions in webview mode

Exit criteria:

- valid math renders in the custom editor
- malformed math produces a visible fallback/error state
- no blank webview due to asset loading

### Phase 3: Source-Editor Features

Status: pending

- preserve local caret and selection during document updates
- add block-aware reveal/focus behavior
- add lightweight error/status display in the custom editor
- improve edit batching so large source edits do not jitter the preview
- make reopen/reload behavior deterministic

Exit criteria:

- typing feels stable
- caret does not jump unexpectedly
- current block preview tracks the user’s position
- editor reload does not lose state

### Phase 4: Math-Aware Editing

Status: pending

- introduce block-level source actions instead of raw textarea-only editing
- add selection mapping between rendered block state and source offsets
- add optional block-focused editing helpers without replacing the source-text model

Exit criteria:

- users can work on math blocks without losing source fidelity
- source offsets remain authoritative
- no hidden alternate document model

### Phase 5: Simple/WASM Migration

Status: pending

- move math parsing/render metadata generation behind the existing math-core bridge
- return structured block data from WASM, not only render strings
- keep VS Code host glue in TypeScript

Exit criteria:

- active-block analysis can come from WASM
- renderer output matches current TypeScript behavior on representative fixtures
- malformed input still degrades safely

## Verification Plan

### Automated

- keep `npm run compile` green for every phase
- extend `src/app/vscode_extension/src/test/gui/mathRendering.test.ts`
- add explicit coverage for:
  - custom editor open path
  - selection sync
  - source edit round-trip
  - malformed math fallback

### Manual

- open the extension development host on `examples/math_demo.spl`
- open the file with `Simple Math Source Editor`
- verify:
  - source pane loads
  - active block preview updates as caret moves
  - malformed math does not blank the webview

## Known Blockers

- full `npm run test:gui` is currently contaminated by unrelated AI command failures
- this makes renderer-log inspection the current trusted signal for math GUI results
- this should be fixed separately from math-editor work to avoid cross-feature confusion

## Next Actions

1. add explicit source-edit round-trip tests for the custom editor
2. add malformed-math fallback coverage in the custom editor
3. open the custom editor from the development host and validate rendering manually
4. only after that, add richer math-aware editing behavior
