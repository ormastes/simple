# Simple 2D Vector Fonts System Test Plan

- System SSpec: `test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl` (7 scenarios)
- Direct interpreter probe: `test/02_integration/rendering/simple_2d_vector_fonts_interpreter_probe.spl`
- Cache unit: `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
- Bitmap integration: `test/02_integration/rendering/engine2d_text_spec.spl`
- Public-path perf: `test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl`
- Bitmap baseline probe: `test/05_perf/graphics_2d/simple_2d_bitmap_text_baseline_probe.spl`
- Manual: `doc/06_spec/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.md` (missing until pure-Simple docgen works)

| ID | Authoritative evidence | Current state |
|---|---|---|
| REQ-001 | failure-safety scenario: empty/missing/malformed/WOFF, full stat/generation atomicity | ready, final run pending |
| REQ-002 | primary scenario: fixed checksum, painted/AA counts, bbox, anchors at 16/32 | ready, final run pending |
| REQ-003 | primary + clipping scenarios; native Rust kerning/line-metric tests | ready, final run pending |
| REQ-004 | Unicode/fallback scenario: fixed Latin-1 and bitmap-fallback oracles | ready, final run pending |
| REQ-005 | failure-safety scenario: invalid sizes plus bitmap restoration | ready, final run pending |
| REQ-006 | exact 7-hit warm scenario; face generation invalidation; cache unit size/generation cases | ready, final run pending |
| REQ-007 | bitmap-default scenario + existing bitmap integration | ready, final run pending |
| REQ-008 | source review, dependency checks, and runtime guards below | pending final guards |
| REQ-009 | direct interpreter probe plus native system scenario | diagnostic probe pass; pure-Simple pending |
| REQ-010 | generated zero-stub operator manual | missing: pure-Simple docgen blocked |
| NFR-001 | 31-pair public-path perf: exact warm requests/hits and zero misses/rasterizations | pending pure-Simple run |
| NFR-002 | public-path cold/warm p50/p95, exact <=75% threshold | pending pure-Simple run |
| NFR-003 | detached HEAD/current bitmap probe, identical checksum, <=5% p50 | missing: pure-Simple baseline run blocked |
| NFR-004 | exact 513-insert and >32 MiB rejection unit; perf cache counters | ready, final run pending |
| NFR-005 | report includes host/binary/fixture/backend/viewport/raw samples/checksum/RSS | pending pure-Simple run |
| NFR-006 | invalid matrix/stat atomicity; Rust snapshot ownership test | ready; outer RSS evidence pending |
| NFR-007 | fixed checksum/bbox/anchor/clipping witnesses | ready, final run pending |
| NFR-008 | source review confirms no hot-path I/O/env/process/font reload | pending final review |
| NFR-009 | direct-runtime and dependency guards | pending final guards |

Final commands, each run once after convergence:

```sh
bin/simple run test/02_integration/rendering/simple_2d_vector_fonts_interpreter_probe.spl
bin/simple test test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl --mode=native
bin/simple test test/01_unit/lib/common/text_layout/font_renderer_spec.spl --mode=native
bin/simple test test/02_integration/rendering/engine2d_text_spec.spl --mode=native
SIMPLE_2D_BITMAP_BASELINE_NS=<retained> SIMPLE_2D_BITMAP_BASELINE_CHECKSUM=<retained> /usr/bin/time -v bin/simple test test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl --mode=native
bin/simple spipe-docgen test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl --output doc/06_spec --no-index
bin/simple deps fast test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl
bin/simple deps normal test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' | wc -l
```
