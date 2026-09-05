# Traits Extended Specification

> <details>

<!-- sdn-diagram:id=traits_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Extended Specification

## Scenarios

### Traits Extended

#### should expose method and combined member queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"methods\"")).to_equal(true)
expect(src.contains("val tr_mth_prefix = tr_mth_type_name + \"__\"")).to_equal(true)
expect(src.contains("if tr_query == \"all_members\"")).to_equal(true)
expect(src.contains("val tr_am_struct_decl = struct_table_lookup(tr_am_type_name)")).to_equal(true)
expect(src.contains("tr_am_result.push(val_make_text(tr_am_mname))")).to_equal(true)
```

</details>

#### should expose enum count class and function queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"enum_count\"")).to_equal(true)
expect(src.contains("val tr_ec_variants_csv = enum_table_lookup(tr_ec_type_name)")).to_equal(true)
expect(src.contains("if tr_query == \"is_class\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_fn\"")).to_equal(true)
expect(src.contains("val tr_if_decl = func_table_lookup(tr_if_name)")).to_equal(true)
```

</details>

#### should expose numeric kind queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"is_integral\"")).to_equal(true)
expect(src.contains("if tr_ii_name == \"i64\": return val_make_bool(true)")).to_equal(true)
expect(src.contains("if tr_query == \"is_float\"")).to_equal(true)
expect(src.contains("if tr_ifl_name == \"f64\": return val_make_bool(true)")).to_equal(true)
expect(src.contains("if tr_query == \"is_numeric\"")).to_equal(true)
expect(src.contains("if tr_in_name == \"f32\": return val_make_bool(true)")).to_equal(true)
```

</details>

#### should expose container kind queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"is_array\"")).to_equal(true)
expect(src.contains("return val_make_bool(tr_ia_first == \"[\")")).to_equal(true)
expect(src.contains("if tr_query == \"is_dict\"")).to_equal(true)
expect(src.contains("return val_make_bool(tr_id_first == \"{\")")).to_equal(true)
```

</details>

#### should expose member type and set member queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = traits_source()
expect(src.contains("if tr_query == \"member_type\"")).to_equal(true)
expect(src.contains("val tr_mt_field_types = decl_get_field_types(tr_mt_struct_decl)")).to_equal(true)
expect(src.contains("return val_make_text(tr_mt_field_types[tr_mt_i])")).to_equal(true)
expect(src.contains("if tr_query == \"set_member\"")).to_equal(true)
expect(src.contains("val_struct_set_field(tr_sm_obj, tr_sm_field, tr_sm_new_val)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
