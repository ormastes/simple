# Stage4 Hir Value Name Dispatch Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Hir Value Name Dispatch Specification

## Scenarios

### Stage4 HIR value-name dispatch

#### keeps lowercase value expressions out of type resolution

- Inspect one lowercase value expression
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect one lowercase value expression")
val (lowering, _) = lower_value_consumer()

expect(lowering.errors.len()).to_equal(0)
```

</details>

#### registers the imported callable after parameter rebinding

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, hir) = lower_value_consumer()

val local = hir.symbols.lookup("emit")
val qualified = hir.symbols.lookup("provider.emit")
val registered = local != nil or qualified != nil
expect(registered).to_be(true)
```

</details>

#### rebinds erased Param elements before reading names or types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lowering = read_file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(lowering).to_contain("val receiver_param: Param = raw_params[0]")
expect(lowering).to_contain("val raw_param: Param = raw_params[first_raw_param]")
expect(lowering).to_contain("self.lower_type(raw_param.type_)")
expect(lowering).to_contain("val param: Param = params[i]")
expect(lowering.contains("raw_params[first_raw_param].type_")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl` |
| Updated | 2026-07-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stage4 HIR value-name dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
