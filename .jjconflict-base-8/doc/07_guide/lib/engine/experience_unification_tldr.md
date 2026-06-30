# Experience Unification — TL;DR

Wave 1 seams joining 2D, 3D, sound, physics on one surface
(`src/lib/nogc_sync_mut/engine/`, default-tier wrapped).

```
            LayerTree (compositor, one gpu_surface)
   z=-5 parallax 2D | z=0 Scene3DLayer (3D out) | z=10 HUD/GUI
            ^ z_paint_order: ascending z = back-to-front
   cameras: render_order i64 (higher draws later)
   loops:   FixedTimestep.advance(dt) -> steps; interpolation_alpha()
   audio:   BusGraph (dB, DAG to master) over AudioGroupTree (linear)
   physics: audit S1-S10 -> dimension-generic core (next waves)
```

- `Scene3DLayer.create/attach`, `display_entry()`, `z_paint_order([i64])` —
  3D frame as a CompositeLayer; no shared 2D/3D depth buffer.
- `render_order` on `camera`/`camera3d`/`CameraData`; `sort_camera_orders`,
  `camera_draws_after`.
- `BusGraph.add_bus/route/set_muted/effective_gain` — gain = ∏ 10^(db/20);
  cycles rejected; muted parent zeroes descendants.
- `FixedTimestep.create(fixed_dt, max_substeps)` — cap drains to zero
  (anti spiral-of-death); alpha in [0,1).
- Interpreter `List<T>()` nil bug blocks LayerTree specs → compiled GUI lane
  (`doc/08_tracking/bug/interpreter_list_generic_nil_2026-06-12.md`).

Full guide: [experience_unification.md](experience_unification.md)
