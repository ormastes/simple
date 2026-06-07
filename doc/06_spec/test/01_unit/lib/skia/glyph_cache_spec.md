# Skia Glyph Cache Specification

> Tests for GlyphCache — a bounded LRU cache of rasterized glyph bitmaps keyed by (font hash, glyph_id, size). Mirrors Skia's SkGlyphCache / SkStrikeCache.

<!-- sdn-diagram:id=glyph_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glyph_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glyph_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glyph_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Glyph Cache Specification

Tests for GlyphCache — a bounded LRU cache of rasterized glyph bitmaps keyed by (font hash, glyph_id, size). Mirrors Skia's SkGlyphCache / SkStrikeCache.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-GLC-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/glyph_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for GlyphCache — a bounded LRU cache of rasterized glyph bitmaps
keyed by (font hash, glyph_id, size). Mirrors Skia's SkGlyphCache /
SkStrikeCache.

## Scenarios

### glyph_cache

#### glyph_cache_new: creates cache with zero entries and given capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(16)
expect(cache.size()).to_equal(0)
expect(cache.capacity).to_equal(16)
```

</details>

#### glyph_cache_key_equal: compares all key fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = _key(1001, 42, 12 * 256)
expect(glyph_cache_key_equal(base, _key(1001, 42, 12 * 256))).to_equal(true)
expect(glyph_cache_key_equal(base, _key(1002, 42, 12 * 256))).to_equal(false)
expect(glyph_cache_key_equal(base, _key(1001, 43, 12 * 256))).to_equal(false)
expect(glyph_cache_key_equal(base, _key(1001, 42, 13 * 256))).to_equal(false)
```

</details>

#### hash_font: stays stable for same font and changes across family or size

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = sk_font_style_normal()
val alpha_12 = sk_font_new(sk_typeface_from_name("Alpha Sans", style), 12.0)
val alpha_12_again = sk_font_new(sk_typeface_from_name("Alpha Sans", style), 12.0)
val alpha_14 = sk_font_new(sk_typeface_from_name("Alpha Sans", style), 14.0)
val beta_12 = sk_font_new(sk_typeface_from_name("Beta Sans", style), 12.0)
expect(hash_font(alpha_12)).to_equal(hash_font(alpha_12_again))
expect(hash_font(alpha_12) == hash_font(alpha_14)).to_equal(false)
expect(hash_font(alpha_12) == hash_font(beta_12)).to_equal(false)
```

</details>

#### insert then lookup: returns Some(bitmap)

1. cache insert
2. Some
   - Expected: found.width equals `2`
   - Expected: found.height equals `2`
   - Expected: found.pixels.length() equals `4`
   - Expected: found.pixels[0] as i64 equals `7`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(4)
val k = _key(1001, 42, 12 * 256)
val bmp = _make_bitmap(2, 2, 7)
cache.insert(k, bmp)
val got = cache.lookup(k)
match got:
    Some(found):
        expect(found.width).to_equal(2)
        expect(found.height).to_equal(2)
        expect(found.pixels.length()).to_equal(4)
        expect(found.pixels[0] as i64).to_equal(7)
    None:
        fail("Expected cache hit for inserted glyph")
```

</details>

#### lookup: missing key returns None

1. cache insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(4)
val k = _key(1001, 42, 12 * 256)
val missing = _key(9999, 1, 10 * 256)
cache.insert(k, _make_bitmap(1, 1, 3))
val got = cache.lookup(missing)
expect(got).to_be_nil()
```

</details>

#### insert beyond capacity: evicts least-recently-used entry

1. cache insert
2. cache insert
3. cache insert
   - Expected: cache.size() equals `2`
4. Some
   - Expected: b.width equals `1`
   - Expected: b.pixels[0] as i64 equals `3`
5. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(2)
val k1 = _key(1, 1, 10 * 256)
val k2 = _key(1, 2, 10 * 256)
val k3 = _key(1, 3, 10 * 256)
cache.insert(k1, _make_bitmap(1, 1, 1))
cache.insert(k2, _make_bitmap(1, 1, 2))
# k1 is now the LRU entry; inserting k3 should evict k1.
cache.insert(k3, _make_bitmap(1, 1, 3))
expect(cache.size()).to_equal(2)
val got_k1 = cache.lookup(k1)
expect(got_k1).to_be_nil()
val got_k3 = cache.lookup(k3)
match got_k3:
    Some(b):
        expect(b.width).to_equal(1)
        expect(b.pixels[0] as i64).to_equal(3)
    None:
        fail("Expected most recently inserted glyph to remain cached")
```

</details>

#### lookup updates last_used (most recent key survives eviction)

1. cache insert
2. cache insert
3. Some
   - Expected: hit.pixels[0] as i64 equals `10`
4. fail
5. cache insert
6. Some
   - Expected: b1.pixels[0] as i64 equals `10`
7. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(2)
val k1 = _key(2, 1, 12 * 256)
val k2 = _key(2, 2, 12 * 256)
val k3 = _key(2, 3, 12 * 256)
cache.insert(k1, _make_bitmap(1, 1, 10))
cache.insert(k2, _make_bitmap(1, 1, 20))
# Touch k1 so it becomes MRU; k2 is now the LRU candidate.
val touch = cache.lookup(k1)
match touch:
    Some(hit):
        expect(hit.pixels[0] as i64).to_equal(10)
    None:
        fail("Expected lookup to refresh k1 before eviction")
cache.insert(k3, _make_bitmap(1, 1, 30))
# k1 should still be present, k2 should have been evicted.
val got_k1 = cache.lookup(k1)
match got_k1:
    Some(b1):
        expect(b1.pixels.length()).to_be_greater_than(0)
        expect(b1.pixels[0] as i64).to_equal(10)
    None:
        fail("Expected refreshed key to survive eviction")
val got_k2 = cache.lookup(k2)
expect(got_k2).to_be_nil()
```

</details>

#### clear: resets size and tick to 0 and drops old entries

1. cache insert
2. cache insert
3. cache clear
   - Expected: cache.size() equals `0`
   - Expected: cache.tick equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = glyph_cache_new(4)
cache.insert(_key(5, 1, 8 * 256), _make_bitmap(1, 1, 1))
cache.insert(_key(5, 2, 8 * 256), _make_bitmap(1, 1, 2))
expect(cache.size()).to_be_greater_than(0)
expect(cache.tick).to_be_greater_than(0)
cache.clear()
expect(cache.size()).to_equal(0)
expect(cache.tick).to_equal(0)
expect(cache.lookup(_key(5, 1, 8 * 256))).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
