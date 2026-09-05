# surface_layer_spec

> Scene3DLayer pure-decision tests (interpreter-green).

<!-- sdn-diagram:id=surface_layer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=surface_layer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

surface_layer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=surface_layer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# surface_layer_spec

Scene3DLayer pure-decision tests (interpreter-green).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/surface_layer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Scene3DLayer pure-decision tests (interpreter-green).

Covers the 3D↔compositor adapter's pure decision logic WITHOUT constructing a
LayerTree or List: default/explicit z-index, geometry fields, z-index mutation
via the me-method, the derived display entry, and the back-to-front z ordering
oracle.

LayerTree attach/composite integration (the List-backed path) is covered by the
compiled GUI sanity lane, not here: interpreter List construction is broken
(`List<T>()` returns nil in the seed interpreter). See bug doc
`doc/08_tracking/bug/interpreter_list_generic_nil_2026-06-12.md`.

## Scenarios

### Scene3DLayer.create

#### defaults z_index to 0 and exposes target geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = Scene3DLayer.create(42, 1280, 720, 0)
expect(scene.target_id).to_equal(42)
expect(scene.z_index).to_equal(0)
expect(scene.width).to_equal(1280)
expect(scene.height).to_equal(720)
```

</details>

#### carries an explicit z-index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = Scene3DLayer.create(7, 640, 480, 3)
expect(scene.target_id).to_equal(7)
expect(scene.z_index).to_equal(3)
expect(scene.width).to_equal(640)
expect(scene.height).to_equal(480)
```

</details>

#### updates z_index via the me-method

- var scene = Scene3DLayer create
- scene set z index
   - Expected: scene.z_index equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scene = Scene3DLayer.create(7, 640, 480, 0)
scene.set_z_index(20)
expect(scene.z_index).to_equal(20)
```

</details>

### Scene3DLayer.display_entry

#### derives a display entry at the adapter's z-index using target_id when unattached

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = Scene3DLayer.create(99, 800, 600, 5)
val entry = scene.display_entry()
expect(entry.id).to_equal(99)
expect(entry.z_index).to_equal(5)
```

</details>

#### tracks z-index changes in the derived entry

- var scene = Scene3DLayer create
- scene set z index
   - Expected: entry.id equals `11`
   - Expected: entry.z_index equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scene = Scene3DLayer.create(11, 320, 240, 0)
scene.set_z_index(-2)
val entry = scene.display_entry()
expect(entry.id).to_equal(11)
expect(entry.z_index).to_equal(-2)
```

</details>

### z_paint_order

#### sorts z-index values ascending = back-to-front

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ordered = z_paint_order([10, -5, 0])
expect(ordered.len()).to_equal(3)
expect(ordered[0]).to_equal(-5)
expect(ordered[1]).to_equal(0)
expect(ordered[2]).to_equal(10)
```

</details>

#### leaves the input array unchanged (value-type copy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = [10, -5, 0]
val ordered = z_paint_order(src)
expect(ordered[0]).to_equal(-5)
expect(src[0]).to_equal(10)
expect(src[1]).to_equal(-5)
expect(src[2]).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
