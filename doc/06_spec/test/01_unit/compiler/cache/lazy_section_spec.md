# lazy_section_spec

> Lazy Section Loading Specification

<!-- sdn-diagram:id=lazy_section_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_section_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_section_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_section_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lazy_section_spec

Lazy Section Loading Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CACHE-031 to #CACHE-040 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/cache/lazy_section_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Lazy Section Loading Specification

Tests bitmap-tracked on-demand section loading for SHB files.
Uses module-level vars to simulate mutable state (nested closure limitation).

## Scenarios

### LazyShbReader

### bitmap tracking

#### starts with no sections loaded

1. lr reset
   - Expected: lr_section_count() equals `0`
   - Expected: lr_is_loaded(FLAG_FUNCTIONS) is false
   - Expected: lr_is_loaded(FLAG_STRUCTS) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
expect(lr_section_count()).to_equal(0)
expect(lr_is_loaded(FLAG_FUNCTIONS)).to_equal(false)
expect(lr_is_loaded(FLAG_STRUCTS)).to_equal(false)
```

</details>

#### marks section as loaded after first access

1. lr reset
   - Expected: lr_is_loaded(FLAG_FUNCTIONS) is true
   - Expected: lr_section_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
val fns = lr_ensure_functions()
expect(lr_is_loaded(FLAG_FUNCTIONS)).to_equal(true)
expect(lr_section_count()).to_equal(1)
```

</details>

#### tracks multiple sections independently

1. lr reset
2. lr ensure functions
3. lr ensure structs
   - Expected: lr_section_count() equals `2`
   - Expected: lr_is_loaded(FLAG_FUNCTIONS) is true
   - Expected: lr_is_loaded(FLAG_STRUCTS) is true
   - Expected: lr_is_loaded(FLAG_CLASSES) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
lr_ensure_functions()
lr_ensure_structs()
expect(lr_section_count()).to_equal(2)
expect(lr_is_loaded(FLAG_FUNCTIONS)).to_equal(true)
expect(lr_is_loaded(FLAG_STRUCTS)).to_equal(true)
expect(lr_is_loaded(FLAG_CLASSES)).to_equal(false)
```

</details>

### caching behavior

#### loads section data only once

1. lr reset
2. lr ensure functions
3. lr ensure functions
   - Expected: count1 equals `1`
   - Expected: count2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
lr_ensure_functions()
val count1 = lr_get_load_count()
lr_ensure_functions()
val count2 = lr_get_load_count()
expect(count1).to_equal(1)
expect(count2).to_equal(1)
```

</details>

#### returns cached data on second access

1. lr reset
   - Expected: fns1.len() equals `3`
   - Expected: fns2.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
val fns1 = lr_ensure_functions()
val fns2 = lr_ensure_functions()
expect(fns1.len()).to_equal(3)
expect(fns2.len()).to_equal(3)
```

</details>

### section data

#### returns function entries

1. lr reset
   - Expected: fns.len() equals `3`
   - Expected: fns[0] equals `fn_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
val fns = lr_ensure_functions()
expect(fns.len()).to_equal(3)
expect(fns[0]).to_equal("fn_a")
```

</details>

#### returns struct entries

1. lr reset
   - Expected: structs.len() equals `2`
   - Expected: structs[0] equals `Point`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
val structs = lr_ensure_structs()
expect(structs.len()).to_equal(2)
expect(structs[0]).to_equal("Point")
```

</details>

#### returns class entries

1. lr reset
   - Expected: classes.len() equals `1`
   - Expected: classes[0] equals `Widget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
val classes = lr_ensure_classes()
expect(classes.len()).to_equal(1)
expect(classes[0]).to_equal("Widget")
```

</details>

### optimization

#### type-check only loads functions and structs

1. lr reset
2. lr ensure functions
3. lr ensure structs
   - Expected: lr_is_loaded(FLAG_TYPE_LAYOUTS) is false
   - Expected: lr_is_loaded(FLAG_ENUMS) is false
   - Expected: lr_section_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lr_reset()
lr_ensure_functions()
lr_ensure_structs()
expect(lr_is_loaded(FLAG_TYPE_LAYOUTS)).to_equal(false)
expect(lr_is_loaded(FLAG_ENUMS)).to_equal(false)
expect(lr_section_count()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
