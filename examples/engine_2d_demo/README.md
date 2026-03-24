# Simple 2D Engine Demo

A minimal platformer demo targeting the new Simple-native 2D engine.

The example code now uses the new engine path only:
- primitive vector commands instead of Lyon tessellation
- keyboard and mouse input only
- explicit silent audio backend until host audio runtime is wired

The remaining end-to-end blockers are below the demo: window and physics host
runtime support are still missing in the Rust driver, and the self-hosted
`bin/simple_native` run/check path still segfaults.

## Run

```bash
./examples/engine_2d_demo/run.sh
```

Current direct check:

```bash
src/compiler_rust/target/debug/simple examples/engine_2d_demo/main.spl
```

That command currently fails honestly on missing `rt_winit_*` / `rt_rapier2d_*`
runtime support. The wrapper script reports those blockers directly.

## Controls

| Key | Action |
|-----|--------|
| A / Left Arrow | Move left |
| D / Right Arrow | Move right |
| W / Up Arrow / Space | Jump |
| Escape | Quit |

## Scene

- **Blue rectangle** with eyes -- player (dynamic physics body)
- **Green bar** -- ground (static)
- **Brown rectangles** -- floating platforms (static)
- **Red circles** -- obstacles (static)
- **White** background

## Engine Features Used

- `Engine2D.create()` -- window + subsystem initialization
- `GameLoop` with `GameCallbacks` -- fixed-timestep game loop
- `bind_wasd_movement()` / `bind_platformer_defaults()` -- preset input bindings
- `PhysicsWorld2D` -- dynamic/static bodies, box/circle colliders, forces, impulses
- `VectorRenderer` -- fill_rect, fill_circle, stroke_line via direct render commands
- `NodeStore` -- scene graph with position tracking
