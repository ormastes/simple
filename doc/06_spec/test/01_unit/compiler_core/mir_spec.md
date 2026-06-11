# Mir Specification

> <details>

<!-- sdn-diagram:id=mir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Specification

## Scenarios

### Mir

#### should define MIR instruction constructors

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mir_source()
expect(src.contains("val MIR_CONST_INT = 1")).to_equal(true)
expect(src.contains("fn mir_const_int(dest: i64, value: i64) -> i64")).to_equal(true)
expect(src.contains("fn mir_const_float(dest: i64, value: text) -> i64")).to_equal(true)
expect(src.contains("fn mir_binop(kind: i64, dest: i64, left: i64, right: i64) -> i64")).to_equal(true)
expect(src.contains("inst_dest[idx] = dest")).to_equal(true)
```

</details>

#### should define MIR terminators

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mir_source()
expect(src.contains("fn term_goto(target_bb: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_return(value_var: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_return_void() -> i64")).to_equal(true)
expect(src.contains("fn term_if_branch(cond_var: i64, then_bb: i64, else_bb: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_switch(scrutinee: i64, case_values: [i64], case_targets: [i64], default_bb: i64) -> i64")).to_equal(true)
```

</details>

#### should define basic block and function builders

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mir_source()
expect(src.contains("fn bb_new(label: text) -> i64")).to_equal(true)
expect(src.contains("fn bb_add_inst")).to_equal(true)
expect(src.contains("fn bb_set_terminator")).to_equal(true)
expect(src.contains("fn mir_fn_new(name: text, param_names: [text], param_types: [i64], ret_type: i64, is_ext: i64) -> i64")).to_equal(true)
expect(src.contains("fn mir_fn_add_bb")).to_equal(true)
```

</details>

#### should define module storage and debug names

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mir_source()
expect(src.contains("fn mir_module_add_fn(fn_id: i64)")).to_equal(true)
expect(src.contains("fn mir_module_get_fns")).to_equal(true)
expect(src.contains("fn mir_inst_kind_name(kind: i64) -> text")).to_equal(true)
expect(src.contains("if kind == MIR_CONST_INT: return \"ConstInt\"")).to_equal(true)
expect(src.contains("if kind == MIR_ADD: return \"Add\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/mir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mir

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
