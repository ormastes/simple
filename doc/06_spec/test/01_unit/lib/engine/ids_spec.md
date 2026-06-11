# ids_spec

> Engine ID System — Generational Handle Tests

<!-- sdn-diagram:id=ids_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ids_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ids_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ids_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ids_spec

Engine ID System — Generational Handle Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/ids_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine ID System — Generational Handle Tests

Tests RawHandle, NodeId, TextureId type-safe wrappers.

## Scenarios

### Engine IDs

### Generation

#### compares equal generations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g1 = Generation(value: 5)
val g2 = Generation(value: 5)
expect(g1.eq(g2)).to_equal(true)
```

</details>

#### compares unequal generations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g1 = Generation(value: 1)
val g2 = Generation(value: 2)
expect(g1.eq(g2)).to_equal(false)
```

</details>

### RawHandle

#### creates a valid handle with new

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = RawHandle.new(0, 1)
expect(h.is_valid()).to_equal(true)
expect(h.to_index()).to_equal(0)
```

</details>

#### creates an invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = RawHandle.invalid()
expect(h.is_valid()).to_equal(false)
```

</details>

#### compares equal handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = RawHandle.new(3, 2)
val h2 = RawHandle.new(3, 2)
expect(h1.eq(h2)).to_equal(true)
```

</details>

#### compares different handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = RawHandle.new(0, 1)
val h2 = RawHandle.new(1, 1)
expect(h1.eq(h2)).to_equal(false)
```

</details>

#### detects generation mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = RawHandle.new(0, 1)
val h2 = RawHandle.new(0, 2)
expect(h1.eq(h2)).to_equal(false)
```

</details>

### NodeId

#### wraps a valid RawHandle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = RawHandle.new(5, 1)
val nid = NodeId(raw: raw)
expect(nid.is_valid()).to_equal(true)
expect(nid.to_index()).to_equal(5)
```

</details>

#### creates an invalid NodeId

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nid = NodeId.invalid()
expect(nid.is_valid()).to_equal(false)
```

</details>

#### compares equal NodeIds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = NodeId(raw: RawHandle.new(2, 3))
val b = NodeId(raw: RawHandle.new(2, 3))
expect(a.eq(b)).to_equal(true)
```

</details>

### TextureId

#### wraps a valid RawHandle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tid = TextureId(raw: RawHandle.new(0, 1))
expect(tid.is_valid()).to_equal(true)
expect(tid.to_index()).to_equal(0)
```

</details>

#### creates an invalid TextureId

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tid = TextureId.invalid()
expect(tid.is_valid()).to_equal(false)
```

</details>

### SpriteId

#### wraps a valid RawHandle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sid = SpriteId(raw: RawHandle.new(7, 2))
expect(sid.is_valid()).to_equal(true)
expect(sid.to_index()).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
