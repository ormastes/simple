# query_schema_spec

> Tests for query schema discovery tool. Validates that schema lists node types, predicates, and examples.

<!-- sdn-diagram:id=query_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_schema_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_schema_spec

Tests for query schema discovery tool. Validates that schema lists node types, predicates, and examples.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QS-001 to #QS-006 |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for query schema discovery tool.
Validates that schema lists node types, predicates, and examples.

## Scenarios

### ast schema content

#### defines node kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["function", "class", "struct", "enum", "trait", "impl", "import", "field", "val", "var", "*"]
expect(kinds.len()).to_equal(11)
expect(kinds).to_contain("function")
expect(kinds).to_contain("*")
```

</details>

#### defines predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preds = ["name", "return_type", "params", "type", "module", "parent", "kind", "signature", "trait", "visibility"]
expect(preds.len()).to_equal(10)
expect(preds).to_contain("name")
expect(preds).to_contain("return_type")
```

</details>

### semantic schema content

#### defines targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = ["fn", "class", "struct", "enum", "trait", "impl", "import", "type", "field", "val", "var", "*"]
expect(targets.len()).to_equal(12)
expect(targets).to_contain("fn")
expect(targets).to_contain("type")
```

</details>

#### defines comparison operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = ["=", "!=", ">", "<", ">=", "<=", "starts_with", "ends_with", "contains"]
expect(ops.len()).to_equal(9)
expect(ops).to_contain("starts_with")
```

</details>

#### defines function predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_preds = ["calls", "has_method", "implements", "imports"]
expect(fn_preds.len()).to_equal(4)
expect(fn_preds).to_contain("calls")
expect(fn_preds).to_contain("implements")
```

</details>

#### defines numeric fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numeric = ["param_count", "field_count"]
expect(numeric.len()).to_equal(2)
expect(numeric).to_contain("param_count")
expect(numeric).to_contain("field_count")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
