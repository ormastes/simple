# Browser portable snapshot specification

Source: `test/03_system/gui/ui_browser/browser_open_spec.spl`.
Owner: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`.

Status: **Phase1 seed diagnostics PASS, 4/4**. Evidence:
`build/phase-one-ui-diagnostic/browser_open_spec/cycle-one.log`. Native
qualification, measured coverage, screenshots, and `spipe-docgen` validation
remain unverified. The folded source retains its original native-run guidance;
its UNRUN note refers to that still-unrun native route. The `@cover` value is a target.

The scenarios invoke the real HTML/layout/paint pipeline with an explicit
software backend. They assert returned ARGB pixels without needing a browser
process, network, GPU, or display server. The uniquely named public renderer
entry avoids the historical duplicate entry name documented in its owner.

## Scenarios

| Requirement | Scenario | Pixel oracle |
|---|---|---|
| REQ-BROWSER-SNAPSHOT-001 | Configured viewport | 160×120 returns 19,200 pixels; first and last match the CSS background |
| REQ-BROWSER-SNAPSHOT-002 | Visible text | Both 64×48 buffers are complete; blank is white; text changes some, but not all, pixels |
| REQ-BROWSER-SNAPSHOT-003 | Smallest viewport | 1×1 returns exactly one pixel matching its distinct background |
| REQ-BROWSER-SNAPSHOT-004 | Repeat rendering | Both 64×48 buffers are complete and every corresponding pixel matches |

### Configured viewport

1. Render a browser snapshot from HTML with background `#123456` at 160×120.
2. Inspect snapshot pixels and dimensions: require 19,200 pixels and the
   expected ARGB background at both ends of the buffer.

### Visible text

1. Render text and blank browser snapshots with identical white backgrounds,
   black text, zero body margin, and 16px font size at 64×48.
2. Inspect snapshot pixels and dimensions: require two complete buffers,
   uniformly white blank pixels, and a nonempty proper subset changed by `X`.

### Smallest viewport

1. Render the smallest browser snapshot with background `#abcdef` at 1×1.
2. Inspect snapshot pixels and dimensions: require one correctly colored pixel.

### Repeat rendering

1. Render the same browser snapshot twice at 64×48.
2. Inspect both complete snapshot buffers: require both lengths before
   comparing every corresponding pixel, so empty renders cannot pass.

## Remaining browser-open scope

Actual window opening and the `SIMPLE_GUI_TEST` opt-in gate are **incomplete**.
The deleted legacy spec only compared a constant environment-variable name
with itself; that never established gate behavior. Its PPM path/format,
default 1280×720 dimensions, and color-string assertions likewise exercised
no implementation. PPM serialization, CLI defaults, native opening, and gate
behavior still require executable browser-entry evidence. These snapshot
scenarios must not be reported as completion of the entire browser-open scope.

## Execution prerequisites

Use a source-matched self-hosted full CLI or standalone runner with explicit
`--native-backend=llvm` or `--native-backend=cranelift` and
`SIMPLE_NO_STUB_FALLBACK=1`. Preserve actual build/run results. Do not use the
Rust seed, source listing, or load-only interpretation as runtime evidence.
After restoring that prerequisite, run this spec and
`simple spipe-docgen test/03_system/gui/ui_browser/browser_open_spec.spl --output doc/06_spec --no-index`;
require real executed cases and zero docgen stubs separately.

<details>
<summary>Executable SSpec</summary>

The complete source below is reproduced for review; it has not been executed.

```simple
"""
Portable browser snapshot regression scenarios for the UI-rendering team.
The real HTML/layout/paint renderer produces the pixels under assertion.
The software backend makes this lane independent of GPU/display availability.

Run with a source-matched self-hosted test runner and --native-backend=llvm
or --native-backend=cranelift, with SIMPLE_NO_STUB_FALLBACK=1. A file load
or source inventory is not execution evidence. Current repair: runtime UNRUN.

This covers viewport sizing, visible text, the smallest viewport, and repeat
rendering. Browser window opening, PPM serialization, default CLI dimensions,
and the SIMPLE_GUI_TEST opt-in gate still need separate executable evidence.
No screenshot artifact or GUI interaction is claimed by these pixel checks.
"""
# codex-system-test
# @tag:system
# @manual_section: browser portable snapshot smoke
# @cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl 80%
# Coverage percentage is a target, not a measured result.

use std.spec.*
use std.spec.step
use std.gc_async_mut.gpu.browser_engine.simple_web_renderer.{
    simple_web_render_html_to_pixels_with_resolved_engine2d_backend
}

describe "Browser Engine portable snapshot smoke":
    it "should render a full pixel snapshot at the configured viewport size":
        # @req REQ-BROWSER-SNAPSHOT-001
        step("Render a browser snapshot")
        val html = "<html><body style='margin:0;background:#123456'></body></html>"
        val pixels = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, 160, 120, "software")
        step("Inspect snapshot pixels and dimensions")
        expect(pixels.len()).to_equal(19200)
        if pixels.len() == 19200:
            expect(pixels[0]).to_equal(0xFF123456)
            expect(pixels[19199]).to_equal(0xFF123456)

    it "should paint visible text differently from a blank document":
        # @req REQ-BROWSER-SNAPSHOT-002
        step("Render text and blank browser snapshots")
        val text_html = "<html><body style='margin:0;background:#ffffff;color:#000000;font-size:16px'>X</body></html>"
        val blank_html = "<html><body style='margin:0;background:#ffffff;color:#000000;font-size:16px'></body></html>"
        val text_pixels = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(text_html, 64, 48, "software")
        val blank_pixels = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(blank_html, 64, 48, "software")
        step("Inspect snapshot pixels and dimensions")
        expect(text_pixels.len()).to_equal(3072)
        expect(blank_pixels.len()).to_equal(3072)
        if text_pixels.len() == 3072 and blank_pixels.len() == 3072:
            var changed_pixels = 0
            for i in 0..3072:
                expect(blank_pixels[i]).to_equal(0xFFFFFFFF)
                if text_pixels[i] != blank_pixels[i]:
                    changed_pixels = changed_pixels + 1
            expect(changed_pixels).to_be_greater_than(0)
            expect(changed_pixels).to_be_less_than(3072)

    it "should render the 1x1 viewport boundary as exactly one painted pixel":
        # @req REQ-BROWSER-SNAPSHOT-003
        step("Render the smallest browser snapshot")
        val html = "<html><body style='margin:0;background:#abcdef'></body></html>"
        val pixels = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, 1, 1, "software")
        step("Inspect snapshot pixels and dimensions")
        expect(pixels.len()).to_equal(1)
        if pixels.len() == 1:
            expect(pixels[0]).to_equal(0xFFABCDEF)

    it "should reproduce every pixel on repeated software snapshots":
        # @req REQ-BROWSER-SNAPSHOT-004
        step("Render the same browser snapshot twice")
        val html = "<html><body style='margin:0;background:#123456;color:#ffffff;font-size:16px'>X</body></html>"
        val first = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, 64, 48, "software")
        val second = simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, 64, 48, "software")
        step("Inspect both complete snapshot buffers")
        expect(first.len()).to_equal(3072)
        expect(second.len()).to_equal(3072)
        if first.len() == 3072 and second.len() == 3072:
            for i in 0..3072:
                expect(second[i]).to_equal(first[i])
```

</details>
