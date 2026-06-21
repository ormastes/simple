# GUI/Web/2D 8K Perf Status — 2026-06-21

## Evidence

Command:

```bash
SIMPLE_LIB=src bin/simple run examples/06_io/ui/showcase_8k_scroll_gui.spl
```

Result: exit 0.

Smoke viewport: 1280x800, 1,024,000 px.

Correctness:

- ON scroll path equals OFF full repaint with byte-identical buffers.

Default smoke metrics:

| Scenario | OFF mean | ON mean | Dirty pixels | Result |
| --- | ---: | ---: | ---: | --- |
| idle | 189331us | <1us | 0 | retained path skips unchanged frame |
| steady scroll | 189656us | 102040us | 63216 | ~1.8x raster-stage speedup |

The benchmark prints this present limitation: no sub-rect present extern exists,
so on-window present still has a full-frame upload ceiling.

## Full 8K Status

Full 8K proof is not claimed by this run.

Missing retained full-8K evidence row:

- viewport: 7680x4320
- backend: GUI/web/2D backend under test
- binary/source revision
- readback mode and checksum/readback proof
- p50/p95 timing
- RSS or memory budget
- fallback state

Blocker: `8k-host-unavailable-for-this-turn`.

The default smoke run is useful regression evidence, but it must not be counted
as a full 8K GUI/web/2D performance pass.
