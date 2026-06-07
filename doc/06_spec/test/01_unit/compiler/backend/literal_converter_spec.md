# Literal Converter Specification

> <details>

<!-- sdn-diagram:id=literal_converter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=literal_converter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

literal_converter_spec -> std
literal_converter_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=literal_converter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Literal Converter Specification

## Scenarios

### LiteralConverter

#### array conversion (STUB-003 fix)

#### returns Value.Array with all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = [Value.Int(1), Value.Int(2), Value.Int(3)]
val result = LiteralConverter.convert_array(elements)
match result:
    case Value.Array(elems):
        expect(elems.len()).to_equal(3)
    case _:
        expect("not Array").to_equal("Array")
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = LiteralConverter.convert_array([])
match result:
    case Value.Array(elems):
        expect(elems.len()).to_equal(0)
    case _:
        expect("not Array").to_equal("Array")
```

</details>

#### tuple conversion (STUB-003 fix)

#### returns Value.Tuple with all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elements = [Value.String("a"), Value.Int(42)]
val result = LiteralConverter.convert_tuple(elements)
match result:
    case Value.Tuple(elems):
        expect(elems.len()).to_equal(2)
    case _:
        expect("not Tuple").to_equal("Tuple")
```

</details>

#### dict conversion (STUB-003 fix)

#### returns Value.Dict with string keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [(Value.String("x"), Value.Int(1)), (Value.String("y"), Value.Int(2))]
val result = LiteralConverter.convert_dict(pairs)
match result:
    case Value.Dict(entries):
        expect(entries.len()).to_equal(2)
    case _:
        expect("not Dict").to_equal("Dict")
```

</details>

#### handles empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = LiteralConverter.convert_dict([])
match result:
    case Value.Dict(entries):
        expect(entries.len()).to_equal(0)
    case _:
        expect("not Dict").to_equal("Dict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/literal_converter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LiteralConverter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
