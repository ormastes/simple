# Agent Tasks: Simple WM Host and SimpleOS Fullscreen

## Shared Contract
Interfaces: `HostDisplayMode`, `HostSurfaceState`, `HostDisplayTransition`, existing `SharedWmScene`, `TaskbarModel`, `shared_wm_scene_render_to_backend`, and typed Simple Web content artifacts.

Manual steps: `Launch the production WM in a host window`; `Toggle the host surface to fullscreen and restore it`; `Boot SimpleOS into its framebuffer desktop`; `Interact with internal windows and taskbar chrome`; `Validate captured pixels and backend provenance`.

Unimplemented helpers call `fail(...)` or `assert(false)`. Constant-success assertions, fixed markers, synthetic captures, and masked failures are forbidden.

## Lanes
| Lane | Scope | Dependencies |
|---|---|---|
| A Host surface | host compositor/entry, Winit facade, unit tests | Shared contract |
| B Shared rendering | window scene/Draw IR, Web content, renderer tests | Shared contract |
| C SimpleOS | desktop shell, framebuffer scene, QEMU entry/tests | Lane B contract |
| D Evidence/manuals | wrappers, system specs, manuals, guide/report | A-C |
| E Performance | measurement and semantics-preserving optimization | A-D |

Lower-model sidecars implement disjoint A-C slices. `/root` is merge owner, final normal/highest-capability reviewer, and generated-manual reviewer.
