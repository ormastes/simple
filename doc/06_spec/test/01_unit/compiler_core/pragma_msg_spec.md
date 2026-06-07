# Pragma Msg Specification

> <details>

<!-- sdn-diagram:id=pragma_msg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pragma_msg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pragma_msg_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pragma_msg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pragma Msg Specification

## Scenarios

### pragma_msg Built-in

#### should expose pragma_msg as an interpreter builtin

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = builtins_source()
expect(src.contains("pragma_msg(expr)")).to_equal(true)
expect(src.contains("if name == \"pragma_msg\"")).to_equal(true)
```

</details>

#### should evaluate its first argument before printing

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = builtins_source()
expect(src.contains("if arg_eids.len() > 0")).to_equal(true)
expect(src.contains("val pm_val = eval_expr(arg_eids[0])")).to_equal(true)
expect(src.contains("if eval_had_error: return -1")).to_equal(true)
```

</details>

#### should print the argument text and return nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = builtins_source()
expect(src.contains("print val_to_text(pm_val)")).to_equal(true)
expect(src.contains("return val_make_nil()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/pragma_msg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pragma_msg Built-in

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
