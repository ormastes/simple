# Graphics 2D showcase nil-receiver crash

## Status

Open. Blocks `graphics_2d_showcase` standalone readiness.

## Reproduction

```text
bin/simple run examples/06_io/ui/graphics_2d_showcase.spl
runtime error: field access on nil receiver
exit=132
```

The failure occurs before the first Engine2D readback/provenance row. The runtime did not provide a source location. The new app statically covers the public Engine2D primitive families and fails closed, but catalog readiness remains false until execution produces a correct-size nonblank readback.

## Acceptance

- Headless software execution prints backend, readback source, checksum, nonzero count, dimensions, and pixel count.
- The frame is 800x600 and nonblank.
- Requested GPU backends report actual device-readback provenance or fail explicitly.
- GUI mode creates a real window and routes close/Q/Escape without reporting unavailable presentation as success.
