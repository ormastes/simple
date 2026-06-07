# web_paint_cache_spec

> test/perf/web_render_chrome/web_paint_cache_spec.spl

<!-- sdn-diagram:id=web_paint_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_paint_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_paint_cache_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_paint_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_paint_cache_spec

test/perf/web_render_chrome/web_paint_cache_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-8 — Web engine paint pipeline: |
| Category | Web Rendering \| Paint \| Cache |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/web_render_chrome/web_paint_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/web_render_chrome/web_paint_cache_spec.spl

  style/layout cache invalidation, paint-command batching,
  glyph cache, scroll damage tracking.
Verifies:
  - Style/layout cache invalidation is tracked (cache_miss_count)
  - Paint-command batching reduces command count (batch_count < raw_count)
  - Glyph cache hit rate is reported (glyph_hits, glyph_misses)
  - Scroll damage tracking records damaged region (scroll_damage_px)

@cover examples/11_advanced/browser/entity/dom/paint_types.spl

## Scenarios

### web_paint_cache — AC-8: style cache, paint batching, glyph cache, scroll damage

### style/layout cache invalidation

#### AC-8: cache_hit_count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(10, 2, false)
expect(c.cache_hit_count >= 0).to_equal(true)
```

</details>

#### AC-8: cache_miss_count is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(10, 2, false)
expect(c.cache_miss_count >= 0).to_equal(true)
```

</details>

#### AC-8: cache hits are greater than misses in a warm run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(10, 2, false)
expect(c.cache_hit_count > c.cache_miss_count).to_equal(true)
```

</details>

#### AC-8: invalidated flag is false in a stable layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(10, 2, false)
expect(c.invalidated).to_equal(false)
```

</details>

#### AC-8: invalidated flag is true after layout change

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(0, 1, true)
expect(c.invalidated).to_equal(true)
```

</details>

#### AC-8: cache miss count increases on invalidation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: StyleCacheSentinel = make_style_cache(0, 1, true)
expect(c.cache_miss_count > 0).to_equal(true)
```

</details>

### paint-command batching

#### AC-8: raw_command_count is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: PaintBatchSentinel = make_paint_batch(100, 35)
expect(b.raw_command_count > 0).to_equal(true)
```

</details>

#### AC-8: batch_command_count is less than raw_command_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: PaintBatchSentinel = make_paint_batch(100, 35)
expect(b.batch_command_count < b.raw_command_count).to_equal(true)
```

</details>

#### AC-8: batch_ratio_pct is greater than zero (batching reduces commands)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: PaintBatchSentinel = make_paint_batch(100, 35)
expect(b.batch_ratio_pct > 0).to_equal(true)
```

</details>

#### AC-8: batch_ratio_pct is less than 100 (not all commands eliminated)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: PaintBatchSentinel = make_paint_batch(100, 35)
expect(b.batch_ratio_pct < 100).to_equal(true)
```

</details>

#### AC-8: no batching when raw == batched (ratio is 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: PaintBatchSentinel = make_paint_batch(50, 50)
expect(b.batch_ratio_pct).to_equal(0)
```

</details>

### glyph cache

#### AC-8: glyph_hits is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(80, 20)
expect(g.glyph_hits >= 0).to_equal(true)
```

</details>

#### AC-8: glyph_misses is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(80, 20)
expect(g.glyph_misses >= 0).to_equal(true)
```

</details>

#### AC-8: hit_rate_pct is in range 0..100

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(80, 20)
expect(g.hit_rate_pct >= 0).to_equal(true)
expect(g.hit_rate_pct <= 100).to_equal(true)
```

</details>

#### AC-8: hit_rate_pct meets minimum threshold for repeated text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(80, 20)
expect(g.hit_rate_pct >= GLYPH_CACHE_MIN_HIT_RATE_PCT).to_equal(true)
```

</details>

#### AC-8: hit_rate_pct is 80 when 80 hits and 20 misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(80, 20)
expect(g.hit_rate_pct).to_equal(80)
```

</details>

#### AC-8: cold cache has zero hits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g: GlyphCacheSentinel = make_glyph_cache(0, 10)
expect(g.glyph_hits).to_equal(0)
expect(g.hit_rate_pct).to_equal(0)
```

</details>

### scroll damage tracking

#### AC-8: scroll_damage_px is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sd: ScrollDamageSentinel = make_scroll_damage(115200, 2073600)
expect(sd.scroll_damage_px >= 0).to_equal(true)
```

</details>

#### AC-8: full_frame_px is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sd: ScrollDamageSentinel = make_scroll_damage(115200, 2073600)
expect(sd.full_frame_px > 0).to_equal(true)
```

</details>

#### AC-8: scroll damage is partial (less than full frame)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sd: ScrollDamageSentinel = make_scroll_damage(115200, 2073600)
expect(sd.is_partial).to_equal(true)
```

</details>

#### AC-8: scroll_damage_px is less than full_frame_px for partial scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sd: ScrollDamageSentinel = make_scroll_damage(115200, 2073600)
expect(sd.scroll_damage_px < sd.full_frame_px).to_equal(true)
```

</details>

#### AC-8: full frame damage is not partial (is_partial false)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sd: ScrollDamageSentinel = make_scroll_damage(2073600, 2073600)
expect(sd.is_partial).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
