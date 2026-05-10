<!-- codex-research -->
# VS Code Math Editor Panel NFR Options

**Feature:** `vscode_math_editor_panel`  
**Date:** 2026-04-10

## NFR Option 1: Preview-First

**Targets**
- Initial panel open: under 100 ms after command dispatch
- Cursor refresh: under 50 ms
- No panel-side edit model

**Pros**
- Minimal latency and complexity
- Very low memory overhead

**Cons**
- Weakest editor parity

**Effort**
- `S`

## NFR Option 2: Synced Panel

**Targets**
- Initial panel open: under 150 ms on a warm extension host
- Cursor/selection sync: under 50 ms
- Preview refresh after edit: under 100 ms for typical math blocks
- Maintain current inline source-editor behavior as fallback

**Pros**
- Good responsiveness while preserving source-editor behavior
- Balanced complexity

**Cons**
- Requires state synchronization discipline

**Effort**
- `M`

## NFR Option 3: Full Custom Editor

**Targets**
- Initial open: under 200 ms warm
- Edit echo: under 16 ms for common edits
- Undo/redo and search must behave like a source editor
- Multi-editor sync must be deterministic

**Pros**
- Strongest UX if the panel is meant to replace the editor

**Cons**
- Highest maintenance and testing cost
- Biggest risk of regressions

**Effort**
- `L`

## Recommended NFR Target

Choose **Option 2**.

It keeps the panel responsive while avoiding the complexity of a full editor replacement.

