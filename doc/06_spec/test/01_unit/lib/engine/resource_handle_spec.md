# resource_handle_spec

> Engine HandleArena — Generational Index Arena Tests

<!-- sdn-diagram:id=resource_handle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_handle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_handle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_handle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_handle_spec

Engine HandleArena — Generational Index Arena Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/resource_handle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine HandleArena — Generational Index Arena Tests

Tests insert/get, remove invalidation, slot reuse with bumped generation.

## Scenarios

### HandleArena

#### inserts and retrieves a value

1. var arena = HandleArena new
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val handle = arena.insert("hello")
val idx = handle.0
val gen_val = handle.1
val result = arena.get(idx, gen_val)
expect(result).to_equal("hello")
```

</details>

#### returns nil for invalid index

1. var arena = HandleArena new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val result = arena.get(-1, 1)
expect(result).to_be_nil
```

</details>

#### returns nil for out-of-range index

1. var arena = HandleArena new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val result = arena.get(999, 1)
expect(result).to_be_nil
```

</details>

#### removes a value and makes handle stale

1. var arena = HandleArena new
   - Expected: removed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val handle = arena.insert("world")
val idx = handle.0
val gen_val = handle.1
val removed = arena.remove(idx, gen_val)
expect(removed).to_equal(true)
val stale = arena.get(idx, gen_val)
expect(stale).to_be_nil
```

</details>

#### reuses slots with bumped generation

1. var arena = HandleArena new
2. arena remove
   - Expected: idx2 equals `idx1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val h1 = arena.insert("first")
val idx1 = h1.0
val gen1 = h1.1
arena.remove(idx1, gen1)
val h2 = arena.insert("second")
val idx2 = h2.0
val gen2 = h2.1
# Should reuse the same index
expect(idx2).to_equal(idx1)
# Generation should be bumped
expect(gen2).to_be_greater_than(gen1)
```

</details>

#### old handle returns nil after slot reuse

1. var arena = HandleArena new
2. arena remove
   - Expected: new_val equals `replacement`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
val h1 = arena.insert("original")
val idx1 = h1.0
val gen1 = h1.1
arena.remove(idx1, gen1)
val h2 = arena.insert("replacement")
# Old handle should be stale
val old_val = arena.get(idx1, gen1)
expect(old_val).to_be_nil
# New handle should work
val new_val = arena.get(h2.0, h2.1)
expect(new_val).to_equal("replacement")
```

</details>

#### tracks count correctly

1. var arena = HandleArena new
   - Expected: arena.len() equals `0`
   - Expected: arena.len() equals `2`
2. arena remove
   - Expected: arena.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
expect(arena.len()).to_equal(0)
val h1 = arena.insert("a")
val h2 = arena.insert("b")
expect(arena.len()).to_equal(2)
arena.remove(h1.0, h1.1)
expect(arena.len()).to_equal(1)
```

</details>

#### checks emptiness

1. var arena = HandleArena new
   - Expected: arena.is_empty() is true
   - Expected: arena.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arena = HandleArena.new()
expect(arena.is_empty()).to_equal(true)
val h = arena.insert("x")
expect(arena.is_empty()).to_equal(false)
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
