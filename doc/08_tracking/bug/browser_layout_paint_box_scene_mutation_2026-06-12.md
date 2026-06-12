# Browser Layout paint_box Does Not Append RenderScene Commands

Status: Open

**Date:** 2026-06-12
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`
**Severity:** Medium (render-scene feature gap)
**Status:** Open

## Problem

`paint_box(box, scene)` is intended to append fill, border, and text commands to
the browser-engine `RenderScene`, but the caller-visible scene command list stays
unchanged after the call. A direct temporary probe showed:

```text
manual_commands=1
paint_commands=1
cmd[0]=manual
```

The manual `scene.add_command("manual")` call persisted, but the recursive
`paint_box(box, scene)` calls did not append any additional commands.

## Impact

`layout_to_scene(...)` cannot currently be used as reliable positive evidence
for browser paint command output. GUI startup rendering paths that rely on this
low-level browser layout scene may silently produce empty scenes.

## Reproduce

Create a DOM with a body and two child `div` nodes that each have
`background_color` set, run `layout_tree(...)`, create `RenderScene.empty(...)`,
append one manual command, then call `paint_box(box, scene)`. The command count
remains `1` instead of increasing to include the body and child fill commands.

## Next Step

Redesign `paint_box`/`layout_to_scene` to return the updated scene or otherwise
use a mutation shape that survives recursive calls in the interpreter and native
runtime. Add direct SSpec coverage for paint command order once the mutation
contract is fixed.
