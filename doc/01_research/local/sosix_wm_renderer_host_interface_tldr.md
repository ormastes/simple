# SOSIX WM/Renderer Host Interface — TLDR

```text
WM/Web/GUI -> Draw IR -> Engine2D -> async SOSIX display/input/time/file services
```

- SOSIX owns host access, not rendering semantics or transient GPU material.
- Move raw env/file/time/sleep/process/window/input calls behind typed capabilities.
- Async: present/readback, input wait, deadlines, file evidence, QMP/process, window control.
- Keep pure layout/Draw IR/raster logic synchronous and SOSIX-free.
- Capture environment once in an immutable startup snapshot; no hot-path env reads.
- Preserve `(surface generation, frame sequence)` and reject stale completions.
- Batch frames/events; never issue one SOSIX request per pixel or primitive.
- Synchronous compatibility waits use notifications, never unbounded polling.
- Native host evidence remains separate from QEMU/TCG correctness.

