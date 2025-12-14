# Feature #511: UI Structural PatchSet/Diff

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

## Summary
Extend PatchSet with structural operations (insert/remove/replace/move) and reconcile keyed/unkeyed child lists for both GUI and TUI renderers.

## Current State
- PatchSet supports only text/attribute/class updates.
- Renderers lack structural diff/apply logic.

## Next Steps
- Define PatchSet structural ops and subtree encoding.
- Implement keyed diff helper and integrate with render output.
- Update GUI/TUI renderers to apply structural ops and detach bindings on removal.
