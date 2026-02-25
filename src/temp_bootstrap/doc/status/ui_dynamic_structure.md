# Feature #510: UI Dynamic Structure

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

## Summary
Render-time control blocks (`<% if %>`, `<% for %>`) with keyed lists that produce structural changes in the UI tree.

## Current State
- UI parser/IR support only covers static templates and text/attr holes.
- No keyed list semantics or render-time control blocks.

## Next Steps
- Extend UI parser/IR with If/For nodes and keyed attributes.
- Add render-time emission of dynamic children and keyed identifiers.
- Integrate with structural PatchSet/diff (Feature 511) to apply changes in GUI/TUI.
