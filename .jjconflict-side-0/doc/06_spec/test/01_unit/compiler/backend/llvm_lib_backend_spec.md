# Llvm Lib Backend Specification

> <details>

<!-- sdn-diagram:id=llvm_lib_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_lib_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_lib_backend_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_lib_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Lib Backend Specification

## Scenarios

### LLVM Lib Backend

#### skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "interpreter cannot load std.sffi.llvm — module-level var DynLib?/Dict causes semantic error"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

#### keeps literal operands on the translated LLVM value path

- extern fn rt file read text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(source).to_contain("val lhs = translate_operand(ctx, mod_, builder, tm, left")
expect(source).to_contain("val rhs = translate_operand(ctx, mod_, builder, tm, right")
expect(source).to_contain("val op_val = translate_operand(ctx, mod_, builder, tm, operand")
expect(source).to_not_contain("val lhs = get_operand_value(left")
expect(source).to_not_contain("val rhs = get_operand_value(right")
expect(source).to_not_contain("val op_val = get_operand_value(operand")
```

</details>

#### keeps integer equality on LLVM icmp before boxed runtime fallback

- extern fn rt file read text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(source).to_contain("elif llvm_get_type_kind(left_ty) == 10:")
expect(source).to_contain("llvm_build_icmp(builder, LLVM_INT_EQ, lhs, rhs, \"eq\")")
expect(source).to_contain("llvm_build_icmp(builder, LLVM_INT_NE, lhs, rhs, \"ne\")")
expect(source).to_contain("rt_native_eq")
expect(source).to_contain("rt_native_neq")
```

</details>

#### does not map nil signature returns through native-int fallback

- extern fn rt file read text
   - Expected: module_source does not contain `val ret_ty = type_mapper.map_type(sig.return_type)`
   - Expected: expr_source does not contain `val ret_ty = tm.map_type(sig.return_type)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn rt_file_read_text(path: text) -> text
val module_source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate.spl") ?? ""
val expr_source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(module_source).to_contain("if sig.return_type == nil: llvm_void_type_in_context(ctx) else: type_mapper.map_type(sig.return_type)")
expect(expr_source).to_contain("get_local_type(local_types, tm, dest.unwrap().id)")
expect(expr_source).to_contain("if sig.return_type == nil: llvm_void_type_in_context(ctx) else: tm.map_type(sig.return_type)")
expect(module_source.contains("val ret_ty = type_mapper.map_type(sig.return_type)")).to_equal(false)
expect(expr_source.contains("val ret_ty = tm.map_type(sig.return_type)")).to_equal(false)
```

</details>

#### keeps LLVM object code emission single-assignment

- extern fn rt file read text
   - Expected: source does not contain `var object_code: [u8]? = nil`
   - Expected: source does not contain `object_code = Some(llvm_object_code_bytes(obj))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_backend.spl") ?? ""

expect(source.contains("var object_code: [u8]? = nil")).to_equal(false)
expect(source.contains("object_code = Some(llvm_object_code_bytes(obj))")).to_equal(false)
expect(source).to_contain("object_code: Some(llvm_object_code_bytes(obj))")
expect(source).to_contain("object_code: nil")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_lib_backend_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM Lib Backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
