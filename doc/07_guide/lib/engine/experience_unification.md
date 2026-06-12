# Experience Libs Unification — Wave 1 APIs

**Date:** 2026-06-12
**Plan:** `doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md`
**TL;DR:** [experience_unification_tldr.md](experience_unification_tldr.md)

Wave 1 adds the shared seams that let 2D, 3D, sound, and physics compose on one
surface. All modules live in `src/lib/nogc_sync_mut/engine/` and are reachable
from the default tier via `nogc_async_mut.engine.*` wrappers.

## 3D output as a compositor layer — `engine.render.surface_layer`

`Scene3DLayer` registers a 3D frame target as a `CompositeLayer` in the shared
compositor `LayerTree`, so 2D canvases and GUI stack above/below it by z-index.
No shared depth buffer: the 3D layer is opaque color output; world-space 2D
belongs on a texture inside the 3D scene.

```simple
use nogc_sync_mut.engine.render.surface_layer.*

val scene = Scene3DLayer.create(target_id, 1280.0, 720.0, 0)  # pure, no tree
var attached = Scene3DLayer.attach(tree, target_id, 1280.0, 720.0, 0)
val entry = attached.display_entry()        # DisplayEntry(layer_id, z_index)
val order = z_paint_order([10, -5, 0])      # [-5, 0, 10] back-to-front
```

`z_paint_order` mirrors `compositor.stacking.flatten_to_paint_order` ordering
(ascending z = back-to-front). `composite_order(entries)` delegates to the
compositor for attached layers.

## Camera ordering — `engine.component.camera_order`

`camera` / `camera3d` / `CameraData` now carry `render_order: i64` (default 0).
Higher draws later (on top). Pure helpers:

```simple
val sorted = sort_camera_orders([10, -5, 0])   # [-5, 0, 10]
val on_top = camera_draws_after(10, 0)          # true
```

## Audio bus graph — `engine.audio.bus`

FMOD/Godot-style named bus graph in the dB domain, layered over
`AudioGroupTree` (which stays the linear playback-routing layer). Routing must
form a DAG to master; cycles are rejected.

```simple
var g = BusGraph.new()
g.add_bus("sfx", -6.0206, false, "")        # name, volume_db, muted, send("" = master)
g.add_bus("ui", 0.0, false, "sfx")
val gain = g.effective_gain("ui")           # product of 10^(db/20) up the chain ≈ 0.5
g.set_muted("sfx", true)                    # zeroes all descendants
```

## Shared fixed timestep — `engine.core.fixed_timestep`

One accumulator for both `game_loop` and `game_loop3d` (seconds, f64). Cap
drains the accumulator to zero to prevent spiral-of-death.

```simple
var ts = FixedTimestep.create(1.0/60.0, 5)
val steps = ts.advance(frame_delta)         # fixed steps to simulate this frame
val alpha = ts.interpolation_alpha()        # [0,1) render interpolation factor
```

Wiring: replace `clock.consume_fixed_steps()` with `ts.advance(frame.delta.value)`
and pass `ts.interpolation_alpha()` to `on_render` (same call in both loops).

## Physics shared core

Audit only this wave: `.spipe/experience-unify/physics_unify_audit.md` lists the
S1–S10 dimension-generic refactor seams (config/body-store/contact-cache
convergence first; joints, rotation representation, narrowphase stay
per-dimension).

## Specs and known limits

Spec manuals: `doc/06_spec/test/01_unit/lib/engine/{surface_layer,camera_order,
audio_bus,fixed_timestep/fixed_timestep}_spec.md` (interpreter-mode green:
7/4/30/11).

`Scene3DLayer.attach`/`composite_order` integration is covered by the compiled
GUI sanity lane, not interpreter specs — the seed interpreter currently nils
`List<T>()` constructors (`doc/08_tracking/bug/interpreter_list_generic_nil_2026-06-12.md`).
