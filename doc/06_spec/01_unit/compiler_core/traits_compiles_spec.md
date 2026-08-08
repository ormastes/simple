# Traits Compiles Specification

> <details>

<!-- sdn-diagram:id=traits_compiles_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_compiles_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_compiles_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_compiles_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Compiles Specification

## Scenarios

### Traits Compiles

#### should evaluate compiles query without leaking inner errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"compiles\"")).to_equal(true)
expect(src.contains("val old_had_error = eval_had_error")).to_equal(true)
expect(src.contains("val old_error_msg = eval_error_msg")).to_equal(true)
expect(src.contains("eval_had_error = false")).to_equal(true)
expect(src.contains("val compiled_ok = not eval_had_error")).to_equal(true)
expect(src.contains("return val_make_bool(compiled_ok)")).to_equal(true)
```

</details>

#### should return false when compiles has no expression argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"compiles\"")).to_equal(true)
expect(src.contains("return val_make_bool(false)")).to_equal(true)
```

</details>

#### should expose get_annotations query through must_use registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"get_annotations\"")).to_equal(true)
expect(src.contains("if must_use_is_registered(ann_sym)")).to_equal(true)
expect(src.contains("ann_list.push(val_make_text(\"must_use\"))")).to_equal(true)
expect(src.contains("return val_make_array(ann_list)")).to_equal(true)
```

</details>

#### should expose has_annotation query through must_use registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"has_annotation\"")).to_equal(true)
expect(src.contains("if ha_ann == \"must_use\"")).to_equal(true)
expect(src.contains("return val_make_bool(must_use_is_registered(ha_sym))")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_compiles_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits Compiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
