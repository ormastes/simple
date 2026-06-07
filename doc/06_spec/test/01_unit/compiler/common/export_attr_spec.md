# ExportAttr Parsing Specification

> Tests the `ExportAttr` struct and `parse_export_attrs()` function which parses `@export("C")` and `@export("C", name: "custom")` annotations.

<!-- sdn-diagram:id=export_attr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_attr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_attr_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_attr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ExportAttr Parsing Specification

Tests the `ExportAttr` struct and `parse_export_attrs()` function which parses `@export("C")` and `@export("C", name: "custom")` annotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-EXPORT-001 |
| Category | Compiler / Attributes |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/01_unit/compiler/common/export_attr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `ExportAttr` struct and `parse_export_attrs()` function which
parses `@export("C")` and `@export("C", name: "custom")` annotations.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ExportAttr | Struct holding is_export_c and export_name |
| parse_export_attrs | Scans [Attribute] for @export("C") |
| Custom name | Optional name: kwarg for C symbol override |

## Scenarios

### ExportAttr

### parse_export_attrs

#### returns nil when no @export attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [make_unrelated_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### returns nil for empty attribute list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = []
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### parses @export('C') correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [make_export_c_attr()]
val result = parse_export_attrs(attrs)
expect(result.?).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("")
```

</details>

#### parses @export('C', name: 'custom') with custom name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [make_export_c_named_attr("my_calc")]
val result = parse_export_attrs(attrs)
expect(result.?).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("my_calc")
```

</details>

#### returns nil for @export without arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [make_export_no_args_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### returns nil for @export with non-C target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [make_export_python_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### finds @export among multiple attributes

1. make unrelated attr
2. make export c attr
3. make unrelated attr
   - Expected: result.? is true
   - Expected: ea.is_export_c is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [Attribute] = [
    make_unrelated_attr(),
    make_export_c_attr(),
    make_unrelated_attr()
]
val result = parse_export_attrs(attrs)
expect(result.?).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
```

</details>

### ExportAttr struct

#### can be constructed with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ea = ExportAttr(is_export_c: false, export_name: "")
expect(ea.is_export_c).to_equal(false)
expect(ea.export_name).to_equal("")
```

</details>

#### can be constructed with export enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ea = ExportAttr(is_export_c: true, export_name: "my_fn")
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("my_fn")
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


## Related Documentation

- **Requirements:** [SFFI bidirectional class interop](SFFI bidirectional class interop)
- **Plan:** [parsed-questing-goose.md](parsed-questing-goose.md)
- **Design:** [sffi_external_library_pattern.md](sffi_external_library_pattern.md)


</details>
