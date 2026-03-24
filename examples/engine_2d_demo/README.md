# Simple 2D Engine Demo

A minimal platformer demo using the Simple-native 2D game engine.

Demonstrates: window creation, input bindings, scene graph, physics simulation,
and vector shape rendering -- all in ~140 lines of Simple.

## Run

```bash
./examples/engine_2d_demo/run.sh
```

Direct command:

```bash
bin/simple_native run examples/engine_2d_demo/main.spl
```

`bin/simple` in this checkout is a bootstrap-only binary and does not support
`run`.

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
- `VectorRenderer` -- fill_rect, fill_circle for shape rendering
- `NodeStore` -- scene graph with position tracking
