# web_render_page_ppm renders catalog page `overview` in ~430 s (Chrome: 1.3 s)

- Status: open (perf)
- Found: 2026-11-13 by check-chrome-catalog-pixel-diff.shs on Windows
- Binary: C:/dev/simple/bin/simple.exe, 37622272 bytes, mtime 2026-11-13 13:29:24 +0900
  (Rust-built bootstrap seed; prints "bootstrap seed only" warning)

## Repro
```
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_2D_BACKEND=cpu_simd \
  C:/dev/simple/bin/simple.exe run examples/06_io/ui/web_render_page_ppm.spl \
  examples/06_io/ui/web_catalog/overview.html out.ppm 900 760
```
Or: `SIMPLE_BIN=C:/dev/simple/bin/simple.exe sh scripts/check/check-chrome-catalog-pixel-diff.shs --pages overview`

## Measured
`page=overview chrome_ms=1269 simple_ms=430094 mismatch_pct=3.59 max_delta=255` (first run: 447746 ms).
Software (cpu_simd, interpreter) HTML render is ~340x slower than headless Chrome. Output is correct
(3.59% mismatch, PASS); the cost is time only.

## To do
Profile the interpreter path (HTML parse/layout/paint); related prior record:
browser_engine_css_size_quadratic_pixel_render_2026-07-04.md. Re-measure on a pure-Simple/native build.
