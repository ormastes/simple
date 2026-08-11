# seed_interp: explicit i64 default-arg marshalling poisons render-background colors

- Status: open
- Area: Seed interpreter default-argument marshalling; affects `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Found: 2026-07-11 (render color difference between default-arg and explicit-arg calls)

## Summary

Calling `simple_web_layout_render_html_software_pixels(html, width, height, budget_ms: i64)` with an explicit 4th argument (e.g. `30000`, `60000`, `120000`) frequently renders ALL background rectangles as white (pixel count = 0 for expected colors) while text glyphs paint normally and with correct colors. Calling the same function with the budget argument OMITTED (using the default `WEB_RENDER_BUDGET_MS`) renders backgrounds with the correct colors every time.

The degraded flag (`degraded: bool`) is false in both cases, meaning the budget guards never fire and the renderer code path is identical. The same HTML, same dimensions, same expected pixel counts — only the call signature differs.

## Measured behavior

Tested on aarch64 macOS via `bin/release/aarch64-apple-darwin/simple_seed run`.

### Hacker News saved page (34KB, 480×360)

| Call style | #ff6600 px | #f6f6ef px | Status |
|---|---|---|---|
| Default arg (omitted) | 18,226 | 113,932 | ✓ correct |
| Explicit arg: 120000 | 0 | 0 | ✗ white |

### Minimal synthetic test (200×80 table)

HTML: `<html><body style="margin:0"><table bgcolor="#ff6600" width="200" height="30"><tr><td>x</td></tr></table></body></html>`

| Call style | #ff6600 px | Status |
|---|---|---|
| Default arg | 2,544 (× 2 runs) | ✓ correct |
| Explicit arg: 30000 | 0 | ✗ white |
| Explicit arg: 10000 | 0 | ✗ white |
| Explicit arg: 1000 | 0 | ✗ white |

## Repro (standalone probe)

```simple
fn count_color_pixels(html: text, width: i32, height: i32, expected_color: u32) -> i64:
    val pixels_default = simple_web_layout_render_html_software_pixels(html, width, height)
    val pixels_explicit = simple_web_layout_render_html_software_pixels(html, width, height, 30000)
    
    var count_default = 0i64
    var count_explicit = 0i64
    
    # Count #ff6600 (0xFFFF6600) at top level only
    for i in range(pixels_default.len()):
        if pixels_default[i] == expected_color:
            count_default = count_default + 1i64
    
    for i in range(pixels_explicit.len()):
        if pixels_explicit[i] == expected_color:
            count_explicit = count_explicit + 1i64
    
    print("Default-arg: {count_default} pixels")
    print("Explicit 30000: {count_explicit} pixels")
    print("Expected color: {expected_color as text}")

fn main():
    val html = """<html><body style="margin:0"><table bgcolor="#ff6600" width="200" height="30"><tr><td>x</td></tr></table></body></html>"""
    count_color_pixels(html, 200, 80, 0xFFFF6600u32)
```

Expected output:
```
Default-arg: 2544 pixels
Explicit 30000: 2544 pixels
Expected color: 4294967296
```

Observed output:
```
Default-arg: 2544 pixels
Explicit 30000: 0 pixels
Expected color: 4294967296
```

## Intermittency and test flake

The budget-hardening spec (`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl`) passes explicit budgets (`1`, `60000`) with exact-color assertions and usually passes, but flakes intermittently with errors like:

```
expected 4294967295 (white) to equal 4282609920 (expected #ff6600)
```

Previously attributed solely to wall-clock load and scheduler margin in the time budget checks (see `browser_engine_wikipedia_render_perf_2026-07-11.md`), but this marshalling bug may contribute: when the explicit budget argument is corrupted at the call boundary, the renderer logic branches unexpectedly or color lookups fetch stale/uninitialized values, producing white pixels intermittently across multiple test runs.

## Root cause hypothesis

Seed interpreter default-argument marshalling for `i64` parameters at the call boundary. Precedent: seed Option-Some marshalling bug (2026-06-15, see `project_seed_crossmodule_field_option_poison_2026-06-14.md`) where a non-interpreted type was mishandled during cross-module returns; seed u64 high-bit corruption (2026-07-11, see `interp_u64_high_bit_option_unwrap_corruption_2026-07-11.md`) where a u64 value >= 2^63 was reinterpreted as signed in the JIT-bail path.

The function signature is:
```simple
fn simple_web_layout_render_html_software_pixels(
    html: text, 
    width: i32, 
    height: i32, 
    budget_ms: i64 = WEB_RENDER_BUDGET_MS
) -> [u32]
```

When the default is used, the interpreter does not marshal the argument across a call boundary. When explicit, it marshals an i64 value. A corrupted marshalling (e.g., byte-swap, truncation to i32, or double-wrapping in a tagged representation) would cause the renderer to receive a garbage budget, which could short-circuit color rendering via early bailout or uninitialized conditionals.

## Impact

- Any caller threading an explicit render budget (test specs, render probes, the staged-budget work in #39) receives silently incorrect pixels.
- Tests asserting exact background colors flake intermittently when the seed interpreter is used.
- The bug is latent in any function with an explicit `param: i64 = CONST` default-arg that interacts with color, layout, or memory state.

## Next steps

1. Isolate with a minimal seed-side repro: pure function with `x: i64 = CONST` default, taking struct/array-typed siblings, returning a value that depends on `x` (not just printing `x`).
2. Inspect seed interpreter default-argument marshalling in `apply_bootstrap_rewrite()` and `Codegen::codegen_call`.
3. Do NOT apply a renderer-side workaround (e.g., clamping budget or using a sentinel value) — this would mask the defect and allow it to corrupt other i64 default-args.

## Not a renderer logic bug

The renderer code path is identical for both calls:
- Same HTML parse tree.
- Same layout engine.
- Same paint queue.
- Same `degraded` flag (false in both).
- Same pixel buffer and color-paint operations.

The only difference is the i64 value at the call boundary. White pixels (0xFFFFFFFF) appearing instead of expected colors suggests either:
1. The budget value corrupted causes an early return before background rendering.
2. A side effect of the marshalling corrupts the renderer's internal color state.

Tracked in `doc/08_tracking/bug/bug_db.sdn` as `seed_interp_explicit_i64_default_arg_poisons_render_backgrounds`.
