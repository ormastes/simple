# Interpreter Native Buffer Guard Specification

> <details>

<!-- sdn-diagram:id=interpreter_native_buffer_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_native_buffer_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_native_buffer_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_native_buffer_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Native Buffer Guard Specification

## Scenarios

### JS native Buffer argument guards

#### keeps Buffer.isBuffer empty-argument guard before reading arg zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_native_source()
expect(source).to_contain("me _native_node_buffer_is_buffer(arg_vals: [JsValue]) -> JsValue:")
expect(source).to_contain("if arg_vals.len() == 0:")
expect(source).to_contain("return JsValue.Boolean(v: false)")
expect(source).to_contain("val obj_id = _get_obj_id(arg_vals.get(0))")
```

</details>

#### keeps WebAssembly payload parsing on safe arg access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_native_source()
expect(source).to_contain("me _native_webassembly_payload_hex(arg_vals: [JsValue]) -> text:")
expect(source).to_contain("match arg_vals.get(0):")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/js/interpreter_native_buffer_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JS native Buffer argument guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
