# UI Feature Status

This file consolidates UI feature status items that were previously split across separate files.

## Feature #510: UI Dynamic Structure

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

### Summary
Render-time control blocks (`<% if %>`, `<% for %>`) with keyed lists that produce structural changes in the UI tree.

### Current State
- UI parser/IR support only covers static templates and text/attr holes.
- No keyed list semantics or render-time control blocks.

### Next Steps
- Extend UI parser/IR with If/For nodes and keyed attributes.
- Add render-time emission of dynamic children and keyed identifiers.
- Integrate with structural PatchSet/diff (Feature 511) to apply changes in GUI/TUI.

## Feature #511: UI Structural PatchSet/Diff

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

### Summary
Extend PatchSet with structural operations (insert/remove/replace/move) and reconcile keyed/unkeyed child lists for both GUI and TUI renderers.

### Current State
- PatchSet supports only text/attribute/class updates.
- Renderers lack structural diff/apply logic.

### Next Steps
- Define PatchSet structural ops and subtree encoding.
- Implement keyed diff helper and integrate with render output.
- Update GUI/TUI renderers to apply structural ops and detach bindings on removal.

## Feature #512: UI SSR + Hydration

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

### Summary
Server-side render UI to HTML plus hydration manifest, then bind client wasm runtime to the existing DOM/tree without full rerender.

### Current State
- No SSR pipeline or hydration manifest.
- UI runtime only supports client-side instantiate + render.

### Next Steps
- Add server render path (InitIR + RenderWasm) that emits HTML and hydration data.
- Implement client hydration that reuses node IDs and rebuilds binding graph.
- Wire fallback to full rerender on mismatch and integrate with renderer/PatchSet.
