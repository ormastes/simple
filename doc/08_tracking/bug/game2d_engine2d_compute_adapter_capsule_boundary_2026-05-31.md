# Bug: Game2D Engine2D compute adapter needs a capsule boundary design

## Date

2026-05-31

## Context

Phase 6 of `doc/03_plan/render_2d_optimization_plan_2026-05-30.md` asks to
wire the game2d render pipeline through the shared compute-session path.

The current game2d pipeline is in `nogc_sync_mut` / `nogc_async_mut`:

```text
LoopDriver.step()
  -> backend.begin_frame()
  -> app.draw(canvas)
  -> backend.execute_commands(canvas.commands)
  -> backend.end_frame()
```

`Canvas` produces `RenderCommandBuffer` values and `HeadlessBackend`
software-rasterizes them. `Engine2D` and `ComputeDispatch` live in the
`gc_async_mut` GPU family.

## Attempted Minimal Adapter

A narrow adapter was prototyped with this shape:

- own `Engine2D`
- own `ComputeDispatchResult`
- implement the game2d backend surface
- translate `RenderCommandBuffer` commands to `Engine2D` draw calls
- call `dispatch.synchronize_frame()` in `end_frame()`

The prototype was rejected before commit because either placement violates a
runtime-family boundary:

- `gc_async_mut` adapter importing game2d `nogc_*` command/canvas/backend types
  produces `gc_boundary_crossing` warnings.
- `nogc_async_mut` adapter importing `std.gpu.engine2d.Engine2D` and
  `ComputeDispatch` produces `nogc_imports_gc_family` warnings.

## Additional Finding

Direct execution of the temporary adapter spec also exposed that
`Engine2D.create_auto()` reaches an existing unqualified `detect_best_backend()`
call path:

```text
semantic: function `detect_best_backend` not found
```

The current safe Engine2D integration remains the explicit accessor path added
in Phase 6:

- `Engine2D.create_compute_dispatch()`
- `Engine2D.create_compute_dispatch_for_backend(...)`
- `Engine2D.detect_best_compute_backend()`

## Required Design Work

Before implementing the game2d adapter, introduce one of:

1. a shared `std.common` render-command/canvas contract that both game2d and
   Engine2D can depend on, or
2. a higher integration layer outside the restricted runtime families that owns
   both game2d commands and GC GPU Engine2D, or
3. an Engine2D-side command submission API that accepts common command DTOs
   rather than importing game2d backend internals.

Do not wire this by direct cross-family imports; that would make verify fail
the capsule boundary.
