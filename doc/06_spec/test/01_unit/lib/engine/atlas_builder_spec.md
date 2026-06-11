# atlas_builder_spec

> Engine Atlas Builder Tests

<!-- sdn-diagram:id=atlas_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atlas_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atlas_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atlas_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# atlas_builder_spec

Engine Atlas Builder Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/atlas_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Atlas Builder Tests

Tests AtlasBuilder sprite registration, shelf-based packing, and AtlasLayout lookups.

## Scenarios

### AtlasBuilder

#### starts with zero entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = AtlasBuilder.new(1)
expect(builder.entry_count()).to_equal(0)
```

</details>

#### adds sprite entries

1. var builder = AtlasBuilder new
2. builder add sprite
3. builder add sprite
   - Expected: builder.entry_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(1)
builder.add_sprite("hero", 32, 32)
builder.add_sprite("enemy", 16, 16)
expect(builder.entry_count()).to_equal(2)
```

</details>

#### clears all entries

1. var builder = AtlasBuilder new
2. builder add sprite
3. builder clear
   - Expected: builder.entry_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(1)
builder.add_sprite("hero", 32, 32)
builder.clear()
expect(builder.entry_count()).to_equal(0)
```

</details>

#### packs a single sprite

1. var builder = AtlasBuilder new
2. builder add sprite
   - Expected: layout.sprite_count() equals `1`
   - Expected: s.x equals `0`
   - Expected: s.y equals `0`
   - Expected: s.width equals `32`
   - Expected: s.height equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(0)
builder.add_sprite("hero", 32, 32)
val layout = builder.pack()
expect(layout.sprite_count()).to_equal(1)
val sp = layout.find_sprite("hero")
if val Some(s) = sp:
    expect(s.x).to_equal(0)
    expect(s.y).to_equal(0)
    expect(s.width).to_equal(32)
    expect(s.height).to_equal(32)
```

</details>

#### packs multiple sprites on one shelf

1. var builder = AtlasBuilder new
2. builder add sprite
3. builder add sprite
   - Expected: layout.sprite_count() equals `2`
   - Expected: a.y equals `b.y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(0)
builder.add_sprite("a", 16, 32)
builder.add_sprite("b", 16, 32)
val layout = builder.pack()
expect(layout.sprite_count()).to_equal(2)
# Both same height, should be on same shelf
val sa = layout.find_sprite("a")
val sb = layout.find_sprite("b")
if val Some(a) = sa:
    if val Some(b) = sb:
        # Same y (same shelf)
        expect(a.y).to_equal(b.y)
```

</details>

#### packs with padding between sprites

1. var builder = AtlasBuilder new
2. builder add sprite
3. builder add sprite
   - Expected: layout.sprite_count() equals `2`
   - Expected: b.x equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(2)
builder.add_sprite("a", 10, 10)
builder.add_sprite("b", 10, 10)
val layout = builder.pack()
expect(layout.sprite_count()).to_equal(2)
# With padding=2, second sprite should start at x=12
val sb = layout.find_sprite("b")
if val Some(b) = sb:
    expect(b.x).to_equal(12)
```

</details>

#### computes atlas dimensions

1. var builder = AtlasBuilder new
2. builder add sprite
3. builder add sprite
   - Expected: layout.width equals `32`
   - Expected: layout.height equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(0)
builder.add_sprite("a", 16, 32)
builder.add_sprite("b", 16, 32)
val layout = builder.pack()
# Two 16-wide sprites side by side = 32 wide, 32 tall
expect(layout.width).to_equal(32)
expect(layout.height).to_equal(32)
```

</details>

### AtlasLayout

#### returns nil for missing sprite name

1. var builder = AtlasBuilder new
2. builder add sprite
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = AtlasBuilder.new(0)
builder.add_sprite("hero", 32, 32)
val layout = builder.pack()
val missing = layout.find_sprite("nonexistent")
var found = false
if val Some(m) = missing:
    found = true
expect(found).to_equal(false)
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
