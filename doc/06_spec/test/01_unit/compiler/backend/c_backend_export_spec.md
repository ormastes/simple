# C Backend Export Wrapper Specification

> Checks that the C backend emits exported symbols using the same ABI-visible names as the header generators. In particular, standalone exported functions must use the `spl_` prefix unless the user provides an explicit custom name.

<!-- sdn-diagram:id=c_backend_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_backend_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_backend_export_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_backend_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend Export Wrapper Specification

Checks that the C backend emits exported symbols using the same ABI-visible names as the header generators. In particular, standalone exported functions must use the `spl_` prefix unless the user provides an explicit custom name.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR #SFFI-EXPORT-ABI |
| Category | Compiler / Backend / C Export |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/backend/c_backend_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks that the C backend emits exported symbols using the same ABI-visible
names as the header generators. In particular, standalone exported functions
must use the `spl_` prefix unless the user provides an explicit custom name.

## Scenarios

### C backend export wrappers

#### prefixes standalone exported function names with spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_exported_fn("__simple_add_numbers", "")
val module = make_module_with_export(func)
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("extern \"C\" int32_t spl_add_numbers(")
expect(output).to_not_contain("extern \"C\" int32_t add_numbers(")
```

</details>

#### preserves explicit custom export names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_exported_fn("__simple_add_numbers", "custom_add")
val module = make_module_with_export(func)
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("extern \"C\" int32_t custom_add(")
expect(output).to_not_contain("extern \"C\" int32_t spl_add_numbers(")
```

</details>

#### emits typed opaque-handle wrappers for exported classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module_with_exported_type()
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("struct spl_Calculator {")
expect(output).to_contain("Calculator inner;")
expect(output).to_contain("extern \"C\" spl_Calculator_t spl_Calculator_create(")
expect(output).to_contain("obj->inner.precision = precision;")
expect(output).to_contain("extern \"C\" int32_t spl_Calculator_add(spl_Calculator_t self")
expect(output).to_contain("__simple_Calculator_add(&self->inner")
```

</details>

#### emits bitfield syntax in backend type definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_module_with_bitfield_type()
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("struct GpioRegister_s {")
expect(output).to_contain("uint8_t mode : 4;")
expect(output).to_contain("bool output : 1;")
expect(output).to_contain("bool input : 1;")
expect(output).to_contain("uint8_t speed : 2;")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
