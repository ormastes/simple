# i64.to_u32 Interpreter Method Resolution Specification

> Regression test for the interpreter gap where calling `.to_u32()` (and sibling numeric conversion methods) on an i64 receiver inside the Rust bootstrap interpreter failed with `method 'to_u32' not found on type 'i64'`.

<!-- sdn-diagram:id=int_to_u32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=int_to_u32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

int_to_u32_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=int_to_u32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i64.to_u32 Interpreter Method Resolution Specification

Regression test for the interpreter gap where calling `.to_u32()` (and sibling numeric conversion methods) on an i64 receiver inside the Rust bootstrap interpreter failed with `method 'to_u32' not found on type 'i64'`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-TO-U32 |
| Category | Interpreter |
| Difficulty | 1/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/int_to_u32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the interpreter gap where calling `.to_u32()` (and sibling
numeric conversion methods) on an i64 receiver inside the Rust bootstrap
interpreter failed with `method 'to_u32' not found on type 'i64'`.

The fix lives in `handle_int_methods` (src/compiler_rust/compiler/src/
interpreter_method/primitives.rs) and the nested-call dispatch mirror in
`interpreter_helpers/method_dispatch.rs`. Both paths now map `to_i8`, `to_i16`,
`to_i32`, `to_i64`, `to_u8`, `to_u16`, `to_u32`, `to_u64` on Int receivers
through `cast_int_to_numeric`, matching the `expr as <T>` cast semantics.

This spec exercises every conversion variant so any future regression in the
primitive method table is caught immediately.

## Scenarios

### i64 numeric conversion methods

#### resolves to_u32 on a plain int receiver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 255
expect(n.to_u32() == 255).to_be_true()
```

</details>

#### resolves to_u32 on an int field read through a struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntHolder(v: 128)
expect(s.v.to_u32() == 128).to_be_true()
```

</details>

#### resolves to_u32 chained with bit shift (mirrors Color.to_u32 pattern)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: i64 = 0x12
val g: i64 = 0x34
val b: i64 = 0x56
val a: i64 = 0xFF
val packed = (a.to_u32() << 24) | (r.to_u32() << 16) | (g.to_u32() << 8) | b.to_u32()
expect(packed == 0xFF123456).to_be_true()
```

</details>

#### resolves to_u8 / to_u16 / to_u64 siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 42
expect(n.to_u8() == 42).to_be_true()
expect(n.to_u16() == 42).to_be_true()
expect(n.to_u64() == 42).to_be_true()
```

</details>

#### resolves to_i8 / to_i16 / to_i32 / to_i64 siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 7
expect(n.to_i8() == 7).to_be_true()
expect(n.to_i16() == 7).to_be_true()
expect(n.to_i32() == 7).to_be_true()
expect(n.to_i64() == 7).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
