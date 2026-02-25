# Feature #512: UI SSR + Hydration

**Status**: Not implemented (planned, see `doc/plans/24_ui_dynamic_structure_and_hydration.md`)  
**Difficulty**: 5  
**Importance**: 4

## Summary
Server-side render UI to HTML plus hydration manifest, then bind client wasm runtime to the existing DOM/tree without full rerender.

## Current State
- No SSR pipeline or hydration manifest.
- UI runtime only supports client-side instantiate + render.

## Next Steps
- Add server render path (InitIR + RenderWasm) that emits HTML and hydration data.
- Implement client hydration that reuses node IDs and rebuilds binding graph.
- Wire fallback to full rerender on mismatch and integrate with renderer/PatchSet.
