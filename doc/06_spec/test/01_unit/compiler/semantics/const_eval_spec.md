# Const Eval Specification

> <details>

<!-- sdn-diagram:id=const_eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=const_eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

const_eval_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=const_eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Eval Specification

## Scenarios

### ConstValue text formatting

#### formats nested values through the typed formatter

- ConstValue Int
- ConstValue Array
   - Expected: value.to_text() equals `(7, [true, "ok"])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = ConstValue.Tuple([
    ConstValue.Int(7),
    ConstValue.Array([ConstValue.Bool(true), ConstValue.String("ok")])
])

expect(value.to_text()).to_equal("(7, [true, \"ok\"])")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/const_eval_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ConstValue text formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
