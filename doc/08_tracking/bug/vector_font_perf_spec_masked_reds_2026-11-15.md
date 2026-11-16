# Vector font perf spec: a loader failure hid two vector-cache reds

Status: OPEN (the loader half is fixed), 2026-11-15, branch `work/bitmap-scale1-20261115`.

## Loader (fixed)

`1fc1852855a` (2026-11-09) switched
`test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl` from writing
the fixture to disk plus `load_font` over to `Engine2D.load_font_bytes`. That
API takes the selected, provenance-gated lane:
`FontRasterizer._load_selected_bytes` returns `invalid()` when
`selected_font_asset_identity_for_path(path) == ""`, and the 400-byte
ttf-parser-demo fixture is not a registry asset.

Probe of each loader check on that fixture:

| check | value |
|---|---|
| identity | `""` |
| validate | `true` |
| supported | `true` |

So the row returned the all-zero evidence early: every assertion failed and
the bitmap block never ran.

Fix: write the file and take the unmanaged lane again, as
`simple_2d_vector_fonts_spec.spl` does. `load_font` then returns true with
identity `unmanaged=...simple_ascii.ttf#0;bytes=400;axes=default`.

## Open: two vector-cache assertions (the masked reds)

Run on seed 59635056 B with load 3.3:

```
cold_p50_ns=35694606 warm_p50_ns=33233222   (needs warm*100 <= cold*75)
warm_hits=651/217 warm_misses=0 warm_rasterizations=0
```

1. **Hit count.** `warm_hits` is exactly 3x `warm_requests`, where requests =
   `CONTENT.len() * 31` = 7 * 31 = 217. Each glyph lookup on a warm draw counts
   three cache hits; the count would fit lookups from three callers per glyph
   (measure, layout, paint). Either the spec's request count or the counter's
   unit is wrong. That is an owner call, so the assertion was not touched.
2. **Warm speed-up.** The warm draw is only 7 % faster than the cold draw
   (needs 25 %). With zero rasterizations on the warm side, the 33 ms per draw
   of 7 glyphs is not raster cost. Not yet profiled.

The bitmap assertions in the same row pass: checksum 772523490 matches the
probe, and p50 3,031,625 ns against the 3,143,803 ns baseline.
