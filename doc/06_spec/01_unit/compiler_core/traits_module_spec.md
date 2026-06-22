# Traits Module Specification

> <details>

<!-- sdn-diagram:id=traits_module_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_module_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_module_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_module_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Module Specification

## Scenarios

### Traits Module

#### should return the active module path for module_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"module_name\"")).to_equal(true)
expect(src.contains("return val_make_text(module_get_path())")).to_equal(true)
```

</details>

#### should expose identifier query with no argument as empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"identifier\"")).to_equal(true)
expect(src.contains("if arg_eids.len() >= 2")).to_equal(true)
expect(src.contains("return val_make_text(\"\")")).to_equal(true)
```

</details>

#### should return bare identifier names without evaluating them

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if expr_get(id_eid).tag == 6")).to_equal(true)
expect(src.contains("return val_make_text(expr_get(id_eid).s_val)")).to_equal(true)
```

</details>

#### should evaluate non identifier arguments before converting to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("val id_val = eval_expr(id_eid)")).to_equal(true)
expect(src.contains("if eval_had_error: return -1")).to_equal(true)
expect(src.contains("return val_make_text(val_to_text(id_val))")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_module_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits Module

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
