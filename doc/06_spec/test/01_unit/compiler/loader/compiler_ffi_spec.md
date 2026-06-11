# Compiler Ffi Specification

> <details>

<!-- sdn-diagram:id=compiler_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_ffi_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Ffi Specification

## Scenarios

### Compiler Ffi

#### creates a compiler context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CompilerContext.create()
expect(ctx.alive).to_equal(true)
```

</details>

#### builds primitive and named type info

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(make_int_type(64, true).type_name).to_equal("i64")
expect(make_float_type(32).type_name).to_equal("f32")
expect(make_bool_type().type_name).to_equal("bool")
expect(make_string_type().type_name).to_equal("string")
expect(make_named_type("Widget").type_name).to_equal("Widget")
```

</details>

#### formats type arguments and byte lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [make_named_type("Int"), make_named_type("String")]
expect(type_args_is_empty(args)).to_equal(false)
expect(type_args_is_empty([])).to_equal(true)
expect(type_to_string(args[0])).to_equal("Int")
expect(code_bytes_len([1, 2, 3])).to_equal(3)
expect(bytes_len([4, 5])).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/compiler_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compiler Ffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
