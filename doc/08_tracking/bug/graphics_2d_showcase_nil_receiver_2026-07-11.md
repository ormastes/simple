# Graphics 2D showcase nil-receiver crash

## Status

Open. Blocks `graphics_2d_showcase` standalone readiness.

## Reproduction

```text
bin/simple run examples/06_io/ui/graphics_2d_showcase.spl
runtime error: field access on nil receiver
exit=132
```

The failure occurs before the first Engine2D readback/provenance row. The app no longer reads argv or environment state; the first application call is `Engine2D.create_offscreen(800, 600)`. Source review found concrete backends were boxed into `Engine2D.backend` and then dereferenced again for capability/name fields. Those values are now precomputed before boxing, but the deployed self-host still traps. The same exit occurs in the existing `engine2d_backend_test.spl`, so this is a shared Engine2D/self-host trait-boxing blocker rather than showcase-only logic. The runtime provides no source stack. Catalog readiness remains false.

## Acceptance

- Headless software execution prints backend, readback source, checksum, nonzero count, dimensions, and pixel count.
- The frame is 800x600 and nonblank.
- Requested GPU backends must match the actual backend and report device-readback provenance with a positive real handle or fail explicitly.
- Five semantic scene samples must demonstrate at least four adjacent differences; background-only output fails.
- GUI mode creates a real window and routes close/Q/Escape without reporting unavailable presentation as success.
