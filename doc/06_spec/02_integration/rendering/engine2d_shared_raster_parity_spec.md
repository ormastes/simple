# engine2d_shared_raster_parity_spec

> Purpose: clear paints an identical surface on both backends

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d_shared_raster_parity_spec

Purpose: clear paints an identical surface on both backends

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: clear paints an identical surface on both backends
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### Engine2D shared-raster parity (emu vs software) — D2 unification gate

#### Family A — core primitives are byte-identical (shared surface)

#### clear paints an identical surface on both backends

- clear paints an identical surface on both backends
- Verify: clear paints an identical surface on both backends
   - Expected: cmp_clear() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear paints an identical surface on both backends")
step("Verify: clear paints an identical surface on both backends")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_clear()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_rect_filled — the primitive emu itself composes from — is identical

- draw_rect_filled — the primitive emu itself composes from — is identical
- Verify: draw_rect_filled — the primitive emu itself composes from — is identical
   - Expected: cmp_rect_filled_core() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect_filled — the primitive emu itself composes from — is identical")
step("Verify: draw_rect_filled — the primitive emu itself composes from — is identical")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_rect_filled_core()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_image blits an identical surface

- draw_image blits an identical surface
- Verify: draw_image blits an identical surface
   - Expected: cmp_image_core() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_image blits an identical surface")
step("Verify: draw_image blits an identical surface")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_image_core()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### Family B — emu-delegating ops stay byte-exact

#### draw_gradient_rect_h matches its emu delegate

- draw_gradient_rect_h matches its emu delegate
- Verify: draw_gradient_rect_h matches its emu delegate
   - Expected: cmp_gradient_rect_h() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_gradient_rect_h matches its emu delegate")
step("Verify: draw_gradient_rect_h matches its emu delegate")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_gradient_rect_h()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_rect_blend matches emu and hits the src-over anchor 0x101E2D3C

- draw_rect_blend matches emu and hits the src-over anchor 0x101E2D3C
- Verify: draw_rect_blend matches emu and hits the src-over anchor 0x101E2D3C
   - Expected: cmp_rect_blend() equals `0`
   - Expected: anchor_rect_blend() equals `0x101E2D3Cu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect_blend matches emu and hits the src-over anchor 0x101E2D3C")
step("Verify: draw_rect_blend matches emu and hits the src-over anchor 0x101E2D3C")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_rect_blend()).to_equal(0)  # oracle: value fixed by the spec contract
expect(anchor_rect_blend()).to_equal(0x101E2D3Cu32)
```

</details>

#### draw_image_blend matches emu and hits the src-over anchor 0x101E2D3C

- draw_image_blend matches emu and hits the src-over anchor 0x101E2D3C
- Verify: draw_image_blend matches emu and hits the src-over anchor 0x101E2D3C
   - Expected: cmp_image_blend() equals `0`
   - Expected: anchor_image_blend() equals `0x101E2D3Cu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_image_blend matches emu and hits the src-over anchor 0x101E2D3C")
step("Verify: draw_image_blend matches emu and hits the src-over anchor 0x101E2D3C")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_image_blend()).to_equal(0)  # oracle: value fixed by the spec contract
expect(anchor_image_blend()).to_equal(0x101E2D3Cu32)
```

</details>

#### Family C — independently written ops that ARE byte-exact

#### draw_rect (opaque outline) is byte-identical to emu

- draw_rect (opaque outline) is byte-identical to emu
- Verify: draw_rect (opaque outline) is byte-identical to emu
   - Expected: cmp_rect_opaque() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect (opaque outline) is byte-identical to emu")
step("Verify: draw_rect (opaque outline) is byte-identical to emu")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_rect_opaque()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_line (thickness 1, Bresenham) is byte-identical to emu

- draw_line (thickness 1, Bresenham) is byte-identical to emu
- Verify: draw_line (thickness 1, Bresenham) is byte-identical to emu
   - Expected: cmp_line_thin() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_line (thickness 1, Bresenham) is byte-identical to emu")
step("Verify: draw_line (thickness 1, Bresenham) is byte-identical to emu")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_line_thin()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_gradient_rect (opaque, integer lerp) is byte-identical to emu

- draw_gradient_rect (opaque, integer lerp) is byte-identical to emu
- Verify: draw_gradient_rect (opaque, integer lerp) is byte-identical to emu
   - Expected: cmp_gradient_rect_opaque() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_gradient_rect (opaque, integer lerp) is byte-identical to emu")
step("Verify: draw_gradient_rect (opaque, integer lerp) is byte-identical to emu")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_gradient_rect_opaque()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_rounded_rect is byte-identical to emu — sw now FILLS (was a 1px OUTLINE bug) [de-faked; canonical: emu]

- draw_rounded_rect is byte-identical to emu — sw now FILLS (was a 1px OUTLINE bug) [de-faked; canonical: emu]
- Verify: draw_rounded_rect is byte-identical to emu — sw now FILLS (was a 1px OUTLINE bug) [de-faked; canonical: emu]
   - Expected: cmp_rounded_rect() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rounded_rect is byte-identical to emu — sw now FILLS (was a 1px OUTLINE bug) [de-faked; canonical: emu]")
step("Verify: draw_rounded_rect is byte-identical to emu — sw now FILLS (was a 1px OUTLINE bug) [de-faked; canonical: emu]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_rounded_rect()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_text is byte-identical to emu — emu delegates to the real 5x7 glyph blit (was a placeholder box) [de-faked; canonical: sw]

- draw_text is byte-identical to emu — emu delegates to the real 5x7 glyph blit (was a placeholder box) [de-faked; canonical: sw]
- Verify: draw_text is byte-identical to emu — emu delegates to the real 5x7 glyph blit (was a placeholder box) [de-faked; canonical: sw]
   - Expected: cmp_text() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text is byte-identical to emu — emu delegates to the real 5x7 glyph blit (was a placeholder box) [de-faked; canonical: sw]")
step("Verify: draw_text is byte-identical to emu — emu delegates to the real 5x7 glyph blit (was a placeholder box) [de-faked; canonical: sw]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_text()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_text_bg is byte-identical to emu — emu delegates to the real AA blit (was bg-fill + placeholder box) [de-faked; canonical: sw]

- draw_text_bg is byte-identical to emu — emu delegates to the real AA blit (was bg-fill + placeholder box) [de-faked; canonical: sw]
- Verify: draw_text_bg is byte-identical to emu — emu delegates to the real AA blit (was bg-fill + placeholder box) [de-faked; canonical: sw]
   - Expected: cmp_text_bg() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text_bg is byte-identical to emu — emu delegates to the real AA blit (was bg-fill + placeholder box) [de-faked; canonical: sw]")
step("Verify: draw_text_bg is byte-identical to emu — emu delegates to the real AA blit (was bg-fill + placeholder box) [de-faked; canonical: sw]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_text_bg()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_rect (alpha outline) is byte-identical to emu — sw now delegates to emu_draw_rect, so alpha edges blend instead of writing raw [reconciled to canonical emu 2026-07-06 (D2)]

- draw_rect (alpha outline) is byte-identical to emu — sw now delegates to emu_draw_rect, so alpha edges blend instead of writing raw [reconciled to canonical emu 2026-07-06 (D2)]
- Verify: draw_rect (alpha outline) is byte-identical to emu — sw now delegates to emu_draw_rect, so alpha edges blend instead of writing raw [reconciled to canonical emu 2026-07-06 (D2)]
   - Expected: cmp_rect_alpha() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect (alpha outline) is byte-identical to emu — sw now delegates to emu_draw_rect, so alpha edges blend instead of writing raw [reconciled to canonical emu 2026-07-06 (D2)]")
step("Verify: draw_rect (alpha outline) is byte-identical to emu — sw now delegates to emu_draw_rect, so alpha edges blend instead of writing raw [reconciled to canonical emu 2026-07-06 (D2)]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_rect_alpha()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_circle (outline) is byte-identical to emu at midpoint-tie radii — sw's decision variable unified to emu's textbook `d<0` (was `d<=0`) [reconciled to canonical emu 2026-07-06 (D2)]

- draw_circle (outline) is byte-identical to emu at midpoint-tie radii — sw's decision variable unified to emu's textbook `d<0` (was `d<=0`) [reconciled to canonical emu 2026-07-06 (D2)]
- Verify: draw_circle (outline) is byte-identical to emu at midpoint-tie radii — sw's decision variable unified to emu's textbook `d<0` (was `d<=0`) [reconciled to canonical emu 2026-07-06 (D2)]
   - Expected: cmp_circle() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle (outline) is byte-identical to emu at midpoint-tie radii — sw's decision variable unified to emu's textbook `d<0` (was `d<=0`) [reconciled to canonical emu 2026-07-06 (D2)]")
step("Verify: draw_circle (outline) is byte-identical to emu at midpoint-tie radii — sw's decision variable unified to emu's textbook `d<0` (was `d<=0`) [reconciled to canonical emu 2026-07-06 (D2)]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_circle()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_circle_filled is byte-identical to emu — emu body replaced with sw's exact per-row distance test (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]

- draw_circle_filled is byte-identical to emu — emu body replaced with sw's exact per-row distance test (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]
- Verify: draw_circle_filled is byte-identical to emu — emu body replaced with sw's exact per-row distance test (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]
   - Expected: cmp_circle_filled() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle_filled is byte-identical to emu — emu body replaced with sw's exact per-row distance test (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]")
step("Verify: draw_circle_filled is byte-identical to emu — emu body replaced with sw's exact per-row distance test (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_circle_filled()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_triangle_filled is byte-identical to emu — emu body replaced with sw's integer barycentric fill (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]

- draw_triangle_filled is byte-identical to emu — emu body replaced with sw's integer barycentric fill (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]
- Verify: draw_triangle_filled is byte-identical to emu — emu body replaced with sw's integer barycentric fill (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]
   - Expected: cmp_triangle() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_triangle_filled is byte-identical to emu — emu body replaced with sw's integer barycentric fill (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]")
step("Verify: draw_triangle_filled is byte-identical to emu — emu body replaced with sw's integer barycentric fill (Metal-exact) [reconciled to canonical sw 2026-07-06 (D2)]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_triangle()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_triangle_filled (collinear, d==0) is byte-identical to emu — barycentric fill no-ops on a zero determinant, same as sw [reconciled to canonical sw 2026-07-06 (D2)]

- draw_triangle_filled (collinear, d==0) is byte-identical to emu — barycentric fill no-ops on a zero determinant, same as sw [reconciled to canonical sw 2026-07-06 (D2)]
- Verify: draw_triangle_filled (collinear, d==0) is byte-identical to emu — barycentric fill no-ops on a zero determinant, same as sw [reconciled to canonical sw 2026-07-06 (D2)]
   - Expected: cmp_triangle_degen() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_triangle_filled (collinear, d==0) is byte-identical to emu — barycentric fill no-ops on a zero determinant, same as sw [reconciled to canonical sw 2026-07-06 (D2)]")
step("Verify: draw_triangle_filled (collinear, d==0) is byte-identical to emu — barycentric fill no-ops on a zero determinant, same as sw [reconciled to canonical sw 2026-07-06 (D2)]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_triangle_degen()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_line (thick) is byte-identical to emu — sw unified to the Vulkan/emu per-point square stamp (was parallel-offset lines) [reconciled to canonical emu 2026-08-15]

- draw_line (thick) is byte-identical to emu — sw unified to the Vulkan/emu per-point square stamp (was parallel-offset lines) [reconciled to canonical emu 2026-08-15]
- Verify: draw_line (thick) is byte-identical to emu — sw unified to the Vulkan/emu per-point square stamp (was parallel-offset lines) [reconciled to canonical emu 2026-08-15]
   - Expected: cmp_line_thick() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_line (thick) is byte-identical to emu — sw unified to the Vulkan/emu per-point square stamp (was parallel-offset lines) [reconciled to canonical emu 2026-08-15]")
step("Verify: draw_line (thick) is byte-identical to emu — sw unified to the Vulkan/emu per-point square stamp (was parallel-offset lines) [reconciled to canonical emu 2026-08-15]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_line_thick()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### Family C — DIVERGENT ops (unification blocked until unified)

#### draw_circle (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw guard]

- draw_circle (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw guard]
- Verify: draw_circle (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw guard]
   - Expected: cmp_circle_r0() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw guard]")
step("Verify: draw_circle (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw guard]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_circle_r0() > 0).to_equal(true)
```

</details>

#### draw_circle_filled (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw]

- draw_circle_filled (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw]
- Verify: draw_circle_filled (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw]
   - Expected: cmp_circle_filled_r0() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle_filled (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw]")
step("Verify: draw_circle_filled (r<=0) diverges — emu stamps a stray center pixel, sw no-ops [canonical: sw]")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(cmp_circle_filled_r0() > 0).to_equal(true)
```

</details>

#### equality matrix

<details>
<summary>Advanced: prints the full per-op equality matrix</summary>

#### prints the full per-op equality matrix

- prints the full per-op equality matrix
- Verify: prints the full per-op equality matrix
   - Expected: cmp_gradient_rect_h() equals `0`
   - Expected: cmp_rect_blend() equals `0`
   - Expected: cmp_image_blend() equals `0`
   - Expected: cmp_rect_opaque() equals `0`
   - Expected: cmp_line_thin() equals `0`
   - Expected: cmp_gradient_rect_opaque() equals `0`
   - Expected: cmp_rect_alpha() equals `0`
   - Expected: cmp_line_thick() equals `0`
   - Expected: cmp_circle() equals `0`
   - Expected: cmp_circle_filled() equals `0`
   - Expected: cmp_rounded_rect() equals `0`
   - Expected: cmp_triangle() equals `0`
   - Expected: cmp_triangle_degen() equals `0`
   - Expected: cmp_text() equals `0`
   - Expected: cmp_text_bg() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints the full per-op equality matrix")
step("Verify: prints the full per-op equality matrix")
# @req: REQ-RENDERING-EngiSharRastPari-001
print("=== ENGINE2D SHARED-RASTER PARITY MATRIX (emu vs software) ===")
print("clear                | EQUAL   | mism={cmp_clear()}      | core primitive (shared)")
print("draw_rect_filled     | EQUAL   | mism={cmp_rect_filled_core()}      | core primitive (shared)")
print("draw_image           | EQUAL   | mism={cmp_image_core()}      | core primitive (shared)")
print("draw_gradient_rect_h | EQUAL   | mism={cmp_gradient_rect_h()}      | delegates to emu")
print("draw_rect_blend      | EQUAL   | mism={cmp_rect_blend()}      | delegates to emu; anchor={anchor_rect_blend()}")
print("draw_image_blend     | EQUAL   | mism={cmp_image_blend()}      | delegates to emu; anchor={anchor_image_blend()}")
print("draw_rect (opaque)   | EQUAL   | mism={cmp_rect_opaque()}      | consolidated to emu 2026-07-06 (D2): sw delegates to emu_draw_rect")
print("draw_line (thin)     | EQUAL   | mism={cmp_line_thin()}      | independent, byte-exact (not consolidated: perf, see D2 notes)")
print("draw_gradient_rect   | EQUAL   | mism={cmp_gradient_rect_opaque()}      | consolidated to emu 2026-07-06 (D2): sw delegates to emu_draw_gradient_rect")
print("draw_rect (alpha)    | EQUAL   | mism={cmp_rect_alpha()}      | reconciled to emu 2026-07-06 (D2): sw delegates to emu_draw_rect")
print("draw_line (thick)    | EQUAL   | mism={cmp_line_thick()}   | reconciled to emu 2026-08-15: sw per-point square stamp (Vulkan-exact)")
print("draw_circle          | EQUAL   | mism={cmp_circle()}      | reconciled to emu 2026-07-06 (D2): sw decision var d<0")
print("draw_circle r<=0     | DIVERGE | mism={cmp_circle_r0()}   | canonical=sw (no-op)")
print("draw_circle_filled   | EQUAL   | mism={cmp_circle_filled()}      | reconciled to sw 2026-07-06 (D2): emu distance-test (Metal-exact)")
print("draw_circle_filled r0| DIVERGE | mism={cmp_circle_filled_r0()}   | canonical=sw (no-op)")
print("draw_rounded_rect    | EQUAL   | mism={cmp_rounded_rect()} | de-faked: sw now FILLS (canonical=emu)")
print("draw_triangle_filled | EQUAL   | mism={cmp_triangle()}      | reconciled to sw 2026-07-06 (D2): emu barycentric (Metal-exact)")
print("draw_triangle degen  | EQUAL   | mism={cmp_triangle_degen()}      | reconciled to sw 2026-07-06 (D2): emu no-ops on d==0")
print("draw_text            | EQUAL   | mism={cmp_text()}   | de-faked: emu delegates to real glyphs (canonical=sw)")
print("draw_text_bg         | EQUAL   | mism={cmp_text_bg()}   | de-faked: emu delegates to AA blit (canonical=sw)")
print("=== END MATRIX ===")
expect(cmp_gradient_rect_h()).to_equal(0)
expect(cmp_rect_blend()).to_equal(0)
expect(cmp_image_blend()).to_equal(0)
expect(cmp_rect_opaque()).to_equal(0)
expect(cmp_line_thin()).to_equal(0)
expect(cmp_gradient_rect_opaque()).to_equal(0)
expect(cmp_rect_alpha()).to_equal(0)
expect(cmp_line_thick()).to_equal(0)
expect(cmp_circle()).to_equal(0)
expect(cmp_circle_filled()).to_equal(0)
expect(cmp_rounded_rect()).to_equal(0)
expect(cmp_triangle()).to_equal(0)
expect(cmp_triangle_degen()).to_equal(0)
expect(cmp_text()).to_equal(0)
expect(cmp_text_bg()).to_equal(0)
```

</details>


</details>

#### GPU-dict pilot — indexed_fill CPU-lane oracle (design cpu_gpu_dual_algorithm)

#### matches the dense-lut formula on a full 256-entry palette (byte 0..255 sweep)

- matches the dense-lut formula on a full 256-entry palette (byte 0..255 sweep)
- Verify: matches the dense-lut formula on a full 256-entry palette (byte 0..255 sweep)
   - Expected: _cmp_indexed_fill(16, 16, _palette_256()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the dense-lut formula on a full 256-entry palette (byte 0..255 sweep)")
step("Verify: matches the dense-lut formula on a full 256-entry palette (byte 0..255 sweep)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_indexed_fill(16, 16, _palette_256())).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the dense-lut formula on a minimal 1-entry palette (every non-zero key is an out-of-range miss)

- matches the dense-lut formula on a minimal 1-entry palette (every non-zero key is an out-of-range miss)
- Verify: matches the dense-lut formula on a minimal 1-entry palette (every non-zero key is an out-of-range miss)
   - Expected: _cmp_indexed_fill(8, 8, [0xFF445566u32]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the dense-lut formula on a minimal 1-entry palette (every non-zero key is an out-of-range miss)")
step("Verify: matches the dense-lut formula on a minimal 1-entry palette (every non-zero key is an out-of-range miss)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_indexed_fill(8, 8, [0xFF445566u32])).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### resolves an out-of-range index to the SAME 0xFFFFFFFF sentinel the design's lut_lookup dense-miss path returns

- resolves an out-of-range index to the SAME 0xFFFFFFFF sentinel the design's lut_lookup dense-miss path returns
- Verify: resolves an out-of-range index to the SAME 0xFFFFFFFF sentinel the design's lut_lookup dense-miss path returns
   - Expected: sw.read_pixels()[0] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves an out-of-range index to the SAME 0xFFFFFFFF sentinel the design's lut_lookup dense-miss path returns")
step("Verify: resolves an out-of-range index to the SAME 0xFFFFFFFF sentinel the design's lut_lookup dense-miss path returns")
# @req: REQ-RENDERING-EngiSharRastPari-001
var idx: [u8] = [250u8]
var sw = _fresh()
sw.indexed_fill(0, 0, 1, 1, idx, [0xFF010203u32, 0xFF040506u32])
expect(sw.read_pixels()[0]).to_equal(0xFFFFFFFFu32)
```

</details>

#### GPU-dict use case #2 — glyph_atlas_blit CPU-lane oracle (design cpu_gpu_dual_algorithm W4)

#### matches the atlas-lookup formula on an in-charset string at scale=2 (font_size=14)

- matches the atlas-lookup formula on an in-charset string at scale=2 (font_size=14)
- Verify: matches the atlas-lookup formula on an in-charset string at scale=2 (font_size=14)
   - Expected: _cmp_text_via_atlas("Hi", 0xFFFFFFFFu32, 14) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the atlas-lookup formula on an in-charset string at scale=2 (font_size=14)")
step("Verify: matches the atlas-lookup formula on an in-charset string at scale=2 (font_size=14)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_text_via_atlas("Hi", 0xFFFFFFFFu32, 14)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the atlas-lookup formula on out-of-charset glyphs at scale=1 (font_size=7) — unknown slot (index 88) resolves identically on both sides

- matches the atlas-lookup formula on out-of-charset glyphs at scale=1 (font_size=7) — unknown slot (index 88) resolves identically on both sides
- Verify: matches the atlas-lookup formula on out-of-charset glyphs at scale=1 (font_size=7) — unknown slot (index 88) resolves identically on both sides
   - Expected: _cmp_text_via_atlas("~$09", 0xFFFFFFFFu32, 7) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the atlas-lookup formula on out-of-charset glyphs at scale=1 (font_size=7) — unknown slot (index 88) resolves identically on both sides")
step("Verify: matches the atlas-lookup formula on out-of-charset glyphs at scale=1 (font_size=7) — unknown slot (index 88) resolves identically on both sides")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_text_via_atlas("~$09", 0xFFFFFFFFu32, 7)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the atlas-lookup formula on a lowercase/digit/space mix

- matches the atlas-lookup formula on a lowercase/digit/space mix
- Verify: matches the atlas-lookup formula on a lowercase/digit/space mix
   - Expected: _cmp_text_via_atlas("Zz 9", 0xFF22C55Eu32, 14) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the atlas-lookup formula on a lowercase/digit/space mix")
step("Verify: matches the atlas-lookup formula on a lowercase/digit/space mix")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_text_via_atlas("Zz 9", 0xFF22C55Eu32, 14)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### W3 — draw_gradient_rect GPU-kernel formula oracle (design cpu_gpu_dual_algorithm_plan W3)

#### matches the lerp formula on an opaque top/bottom pair (h=24, the pre-existing bit-exact case)

- matches the lerp formula on an opaque top/bottom pair (h=24, the pre-existing bit-exact case)
- Verify: matches the lerp formula on an opaque top/bottom pair (h=24, the pre-existing bit-exact case)
   - Expected: _cmp_gradient_kernel_formula(30, 24, 0xFFFF0000u32, 0xFF0000FFu32, 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the lerp formula on an opaque top/bottom pair (h=24, the pre-existing bit-exact case)")
step("Verify: matches the lerp formula on an opaque top/bottom pair (h=24, the pre-existing bit-exact case)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_gradient_kernel_formula(30, 24, 0xFFFF0000u32, 0xFF0000FFu32, 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the lerp formula at h=1 (max_t clamps to 1, no divide-by-zero)

- matches the lerp formula at h=1 (max_t clamps to 1, no divide-by-zero)
- Verify: matches the lerp formula at h=1 (max_t clamps to 1, no divide-by-zero)
   - Expected: _cmp_gradient_kernel_formula(20, 1, 0xFF112233u32, 0xFF445566u32, 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the lerp formula at h=1 (max_t clamps to 1, no divide-by-zero)")
step("Verify: matches the lerp formula at h=1 (max_t clamps to 1, no divide-by-zero)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_gradient_kernel_formula(20, 1, 0xFF112233u32, 0xFF445566u32, 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the lerp+blend formula on a semi-transparent top/bottom pair over a non-black destination

- matches the lerp+blend formula on a semi-transparent top/bottom pair over a non-black destination
- Verify: matches the lerp+blend formula on a semi-transparent top/bottom pair over a non-black destination
   - Expected: _cmp_gradient_kernel_formula(16, 12, 0x80FFFFFFu32, 0x8000FF00u32, 0xFF202020u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the lerp+blend formula on a semi-transparent top/bottom pair over a non-black destination")
step("Verify: matches the lerp+blend formula on a semi-transparent top/bottom pair over a non-black destination")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_gradient_kernel_formula(16, 12, 0x80FFFFFFu32, 0x8000FF00u32, 0xFF202020u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the lerp+blend formula when only one endpoint is transparent (asymmetric alpha)

- matches the lerp+blend formula when only one endpoint is transparent (asymmetric alpha)
- Verify: matches the lerp+blend formula when only one endpoint is transparent (asymmetric alpha)
   - Expected: _cmp_gradient_kernel_formula(16, 12, 0x00FFFFFFu32, 0xFFFF0000u32, 0xFF303030u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the lerp+blend formula when only one endpoint is transparent (asymmetric alpha)")
step("Verify: matches the lerp+blend formula when only one endpoint is transparent (asymmetric alpha)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_gradient_kernel_formula(16, 12, 0x00FFFFFFu32, 0xFFFF0000u32, 0xFF303030u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### Rounded-rect FILL parity fix (2026-07-07) — draw_rounded_rect GPU-kernel formula oracle

#### matches the band/corner formula on the original bug-doc fixture (radius=6, well inside the corner-radius range)

- matches the band/corner formula on the original bug-doc fixture (radius=6, well inside the corner-radius range)
- Verify: matches the band/corner formula on the original bug-doc fixture (radius=6, well inside the corner-radius range)
   - Expected: _cmp_rounded_rect_kernel_formula(30, 24, 6, 0xFFFF0000u32, 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the band/corner formula on the original bug-doc fixture (radius=6, well inside the corner-radius range)")
step("Verify: matches the band/corner formula on the original bug-doc fixture (radius=6, well inside the corner-radius range)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_rounded_rect_kernel_formula(30, 24, 6, 0xFFFF0000u32, 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the band/corner formula when radius == min(w,h)/2 (full corner-radius clamp, a 'stadium' shape)

- matches the band/corner formula when radius == min(w,h)/2 (full corner-radius clamp, a 'stadium' shape)
- Verify: matches the band/corner formula when radius == min(w,h)/2 (full corner-radius clamp, a 'stadium' shape)
   - Expected: _cmp_rounded_rect_kernel_formula(16, 16, 8, 0xFF33CC88u32, 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the band/corner formula when radius == min(w,h)/2 (full corner-radius clamp, a 'stadium' shape)")
step("Verify: matches the band/corner formula when radius == min(w,h)/2 (full corner-radius clamp, a 'stadium' shape)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_rounded_rect_kernel_formula(16, 16, 8, 0xFF33CC88u32, 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the band/corner formula on a narrow strip (h < 2*radius forces the radius clamp on h, not w)

- matches the band/corner formula on a narrow strip (h < 2*radius forces the radius clamp on h, not w)
- Verify: matches the band/corner formula on a narrow strip (h < 2*radius forces the radius clamp on h, not w)
   - Expected: _cmp_rounded_rect_kernel_formula(40, 12, 8, 0xFF4488FFu32, 0xFF101010u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the band/corner formula on a narrow strip (h < 2*radius forces the radius clamp on h, not w)")
step("Verify: matches the band/corner formula on a narrow strip (h < 2*radius forces the radius clamp on h, not w)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_rounded_rect_kernel_formula(40, 12, 8, 0xFF4488FFu32, 0xFF101010u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the band/corner-fill+blend formula on a semi-transparent fill over a non-black destination

- matches the band/corner-fill+blend formula on a semi-transparent fill over a non-black destination
- Verify: matches the band/corner-fill+blend formula on a semi-transparent fill over a non-black destination
   - Expected: _cmp_rounded_rect_kernel_formula(30, 20, 6, 0x80FFFFFFu32, 0xFF202020u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the band/corner-fill+blend formula on a semi-transparent fill over a non-black destination")
step("Verify: matches the band/corner-fill+blend formula on a semi-transparent fill over a non-black destination")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_rounded_rect_kernel_formula(30, 20, 6, 0x80FFFFFFu32, 0xFF202020u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the band/corner formula at radius=0 (plain rect, no corner-arc dispatch)

- matches the band/corner formula at radius=0 (plain rect, no corner-arc dispatch)
- Verify: matches the band/corner formula at radius=0 (plain rect, no corner-arc dispatch)
   - Expected: _cmp_rounded_rect_kernel_formula(20, 14, 0, 0xFF00FF00u32, 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the band/corner formula at radius=0 (plain rect, no corner-arc dispatch)")
step("Verify: matches the band/corner formula at radius=0 (plain rect, no corner-arc dispatch)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_rounded_rect_kernel_formula(20, 14, 0, 0xFF00FF00u32, 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### draw_image (blit) parity-sweep coverage close (2026-07-07) — kernel_blit_image GPU-kernel formula oracle

#### matches the raw-copy formula on a fully on-surface blit

- matches the raw-copy formula on a fully on-surface blit
- Verify: matches the raw-copy formula on a fully on-surface blit
   - Expected: _cmp_blit_kernel_formula(48, 48, 10, 10, 16, 12, _img_varied(16, 12), 0xFF000000u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the raw-copy formula on a fully on-surface blit")
step("Verify: matches the raw-copy formula on a fully on-surface blit")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_blit_kernel_formula(48, 48, 10, 10, 16, 12, _img_varied(16, 12), 0xFF000000u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the raw-copy formula on a blit straddling the right/bottom framebuffer edge

- matches the raw-copy formula on a blit straddling the right/bottom framebuffer edge
- Verify: matches the raw-copy formula on a blit straddling the right/bottom framebuffer edge
   - Expected: _cmp_blit_kernel_formula(48, 48, 40, 40, 16, 16, _img_varied(16, 16), 0xFF101820u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the raw-copy formula on a blit straddling the right/bottom framebuffer edge")
step("Verify: matches the raw-copy formula on a blit straddling the right/bottom framebuffer edge")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_blit_kernel_formula(48, 48, 40, 40, 16, 16, _img_varied(16, 16), 0xFF101820u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the raw-copy formula on a blit straddling the left/top framebuffer edge (negative origin)

- matches the raw-copy formula on a blit straddling the left/top framebuffer edge (negative origin)
- Verify: matches the raw-copy formula on a blit straddling the left/top framebuffer edge (negative origin)
   - Expected: _cmp_blit_kernel_formula(48, 48, -6, -4, 16, 16, _img_varied(16, 16), 0xFF203040u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the raw-copy formula on a blit straddling the left/top framebuffer edge (negative origin)")
step("Verify: matches the raw-copy formula on a blit straddling the left/top framebuffer edge (negative origin)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_blit_kernel_formula(48, 48, -6, -4, 16, 16, _img_varied(16, 16), 0xFF203040u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### matches the raw-copy formula on a blit entirely off-surface (fully clipped, complete no-op)

- matches the raw-copy formula on a blit entirely off-surface (fully clipped, complete no-op)
- Verify: matches the raw-copy formula on a blit entirely off-surface (fully clipped, complete no-op)
   - Expected: _cmp_blit_kernel_formula(48, 48, -20, -20, 8, 8, _img_varied(8, 8), 0xFF556677u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the raw-copy formula on a blit entirely off-surface (fully clipped, complete no-op)")
step("Verify: matches the raw-copy formula on a blit entirely off-surface (fully clipped, complete no-op)")
# @req: REQ-RENDERING-EngiSharRastPari-001
expect(_cmp_blit_kernel_formula(48, 48, -20, -20, 8, 8, _img_varied(8, 8), 0xFF556677u32)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RENDERING-EngiSharRastPari-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae3e39b7e6d8ebe5fe494b82fcda57dbecb3f026bc6b1a5115a045d1d1e34411`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae3e39b7e6d8ebe5fe494b82fcda57dbecb3f026bc6b1a5115a045d1d1e34411`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae3e39b7e6d8ebe5fe494b82fcda57dbecb3f026bc6b1a5115a045d1d1e34411`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl
mirror: doc/06_spec/02_integration/rendering/engine2d_shared_raster_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/engine2d_shared_raster_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/engine2d_shared_raster_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl:676:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear paints an identical surface on both backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl:683:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled — the primitive emu itself composes from — is identical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl:690:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_image blits an identical surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
