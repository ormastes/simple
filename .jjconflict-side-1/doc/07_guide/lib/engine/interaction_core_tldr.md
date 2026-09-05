# Unified 2D Interaction Core — TL;DR

Surface-agnostic hit-test + event core (`std.common.engine.interaction.*`),
shared by GUI/browser/Engine2D. Paint order == hit order via one flattened
key; capture->target->bubble dispatch; pointer capture + hover diffing.
Adapters (widget/browser/WM) not written yet.

```
PaintOrderKey (ascending = on top):
  stacking_context_order > render_layer > z_index > tree_order > insertion_sequence
  used by BOTH hit_stack() sort and (future) renderer sort

hit_stack(proxies, parents, x, y) -> primary + front-to-back hits + ancestor_path
  PointerPolicy.None -> skipped; all others -> bbox test [l,r)x[t,b)
  Painted/Fill/Stroke = reserved, == bbox today; SelfOnly/ChildrenOnly/Translucent = unimplemented

dispatch(event, listeners, ancestor_path):
  CAPTURE (root..target-1) -> TARGET (both kinds) -> BUBBLE (target-1..root)
  listener returns ACTION_* bitmask (no me-mutation across modules -- JIT landmine)
  stopPropagation: blocks ancestors, not current node
  stopImmediatePropagation: blocks current node's remaining listeners too

PointerRouter: capture_pointer/release_pointer -> effective_target() wins
  over hit-test while captured (even outside bounds); hover_diff() -> enter/leave
```

Gotchas: `kind`/`phase` are plain `i32`, not enum fields (interpreter
default-init landmine). Plan: `unified_2d_interaction_2026-07-20.md` Phase 1.

Full guide: [interaction_core.md](interaction_core.md)
