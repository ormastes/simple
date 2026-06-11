# treesitter_incremental_spec

> TreeSitter Incremental Parsing Specification

<!-- sdn-diagram:id=treesitter_incremental_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_incremental_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_incremental_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_incremental_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# treesitter_incremental_spec

TreeSitter Incremental Parsing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-INC-001 |
| Category | Compiler \| Parser |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_incremental_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

TreeSitter Incremental Parsing Specification

@cover src/compiler/10.frontend/treesitter.spl 80%

Tests that outline parsing works correctly on modified source code,
verifying deterministic results and handling of structural changes.

## Scenarios

### TreeSitter Incremental Outline

#### reparses after adding a function

1. var ts1 = TreeSitter new
2. var ts2 = TreeSitter new
   - Expected: o1.functions.len() equals `1`
   - Expected: o2.functions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src1 = "fn a():\n    1\n"
val src2 = "fn a():\n    1\n\nfn b():\n    2\n"
var ts1 = TreeSitter.new(src1)
var ts2 = TreeSitter.new(src2)
val o1 = ts1.parse_outline()
val o2 = ts2.parse_outline()
expect(o1.functions.len()).to_equal(1)
expect(o2.functions.len()).to_equal(2)
```

</details>

#### reparses after removing a function

1. var ts1 = TreeSitter new
2. var ts2 = TreeSitter new
   - Expected: o1.functions.len() equals `2`
   - Expected: o2.functions.len() equals `1`
   - Expected: o2.functions[0].name equals `keep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src1 = "fn keep():\n    1\n\nfn remove():\n    2\n"
val src2 = "fn keep():\n    1\n"
var ts1 = TreeSitter.new(src1)
var ts2 = TreeSitter.new(src2)
val o1 = ts1.parse_outline()
val o2 = ts2.parse_outline()
expect(o1.functions.len()).to_equal(2)
expect(o2.functions.len()).to_equal(1)
expect(o2.functions[0].name).to_equal("keep")
```

</details>

#### reparses after modifying function body

1. var ts1 = TreeSitter new
2. var ts2 = TreeSitter new
   - Expected: o1.functions.len() equals `1`
   - Expected: o2.functions.len() equals `1`
   - Expected: o2.functions[0].name equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src1 = "fn test():\n    42\n"
val src2 = "fn test():\n    99\n"
var ts1 = TreeSitter.new(src1)
var ts2 = TreeSitter.new(src2)
val o1 = ts1.parse_outline()
val o2 = ts2.parse_outline()
expect(o1.functions.len()).to_equal(1)
expect(o2.functions.len()).to_equal(1)
expect(o2.functions[0].name).to_equal("test")
```

</details>

#### produces deterministic results

1. var ts a = TreeSitter new
2. var ts b = TreeSitter new
   - Expected: o_a.functions.len() equals `o_b.functions.len()`
   - Expected: o_a.classes.len() equals `o_b.classes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn x():\n    1\n\nclass Y:\n    v: i64\n"
var ts_a = TreeSitter.new(src)
var ts_b = TreeSitter.new(src)
val o_a = ts_a.parse_outline()
val o_b = ts_b.parse_outline()
expect(o_a.functions.len()).to_equal(o_b.functions.len())
expect(o_a.classes.len()).to_equal(o_b.classes.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
