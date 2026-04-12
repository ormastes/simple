<!-- codex-design -->
# VS Code Rich Editor System Test Plan

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12

## Coverage Goal

Prove that the standalone extension opens `.spl` files in a custom editor with
natural variable-height widgets while keeping the backing `TextDocument`
correct.

## Test Cases

### Activation and open path

- install or launch the standalone extension
- open a `.spl` file with `Simple Rich Source Editor`
- verify the custom editor resolves successfully
- verify the webview boots and receives initial sync

### Variable-height rendering

- open a file with tall math and image blocks
- verify math renders at natural height instead of clamped inline height
- verify image blocks expand vertically without overlapping surrounding lines

### Cursor-aware reveal

- place the cursor outside a renderable block
- verify the rendered widget replaces raw source
- move the cursor into the block
- verify raw source is revealed for editing

### Duplicate block correctness

- create two identical `m{ x + y }` blocks in one file
- verify both render correctly
- edit one block
- verify only the targeted block changes

### Block-local edit round-trip

- edit a math block from the rich editor
- verify the backing `TextDocument` updates
- verify undo/redo works through VS Code text editing semantics

### Error handling

- open malformed math
- verify error widget appears instead of a crash or blank editor
- open a missing image path
- verify image error widget appears with path context

## Manual Verification

- open `examples/math_demo.spl`
- open a file with repeated identical blocks
- open a file with an `img{}` block
- verify light and dark theme rendering
