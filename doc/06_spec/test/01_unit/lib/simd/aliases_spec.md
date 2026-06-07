# SIMD Alias Back-Compat Regression Tests (F2)

> Regression tests for `src/lib/nogc_sync_mut/simd/aliases.spl`:

<!-- sdn-diagram:id=aliases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aliases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aliases_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aliases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SIMD Alias Back-Compat Regression Tests (F2)

Regression tests for `src/lib/nogc_sync_mut/simd/aliases.spl`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-ALIASES |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | In Progress |
| Design | doc/04_architecture/simd_unified_architecture_detail.md §11.3 |
| Source | `test/01_unit/lib/simd/aliases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression tests for `src/lib/nogc_sync_mut/simd/aliases.spl`:

1. **Function-wrapper round-trips (work today):** `vec2f_splat`, `vec4f_splat`,
   `vec8f_splat`, `vec4d_splat`, `vec4i_splat`, `vec4u_splat`, and the
   corresponding `*_from_array` variants.  These were shipped by D4 and must
   not regress.

2. **Type-alias smoke test (A-07):** Verifies that the `type VecXy = FixedVec<T>`
   declarations in aliases.spl do not cause a parse/lint error.  Resolution
   is currently inert (parser_decls.spl:1086 skips type-alias bindings), so
   no import of `{Vec4f}` is attempted here — that would fail until E2 raises
   the import priority.

## Status of Vec4f::splat(1.0) form

The aspirational `Vec4f.splat(1.0)` call requires three prerequisites that
are not yet landed:
  - **F1:** parser fix for `Foo<T>.method()` static dispatch on type-alias names
  - **E2:** import-priority change so `use std.simd.{Vec4f}` resolves to
    aliases.spl rather than the legacy struct in simd_vector_types.spl
  - **D3:** type-alias expansion in resolve_strategies.spl + eval_ops.spl so
    `Vec4f__add` correctly falls through to `FixedVec__add`

Until those land, `Vec4f.splat(1.0)` is NOT tested here.  See
doc/08_tracking/bug/simd_alias_shadow_e2.md for the full fix sequence.

All tests run in interpreter mode using the function-wrapper API only.

## Scenarios

### SIMD back-compat alias wrappers — f32

#### A-01: vec4f_splat produces 4-lane f32 vector with correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec4f_splat(3.14)
val n = v.lanes()
expect(n).to_equal(4)
val arr = v.to_array()
expect(arr[0]).to_equal(3.14)
expect(arr[3]).to_equal(3.14)
```

</details>

#### A-02: vec2f_splat and vec8f_splat produce correct lane counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v2 = vec2f_splat(1.0)
expect(v2.lanes()).to_equal(2)

val v8 = vec8f_splat(2.0)
expect(v8.lanes()).to_equal(8)
```

</details>

#### A-03: vec4f_from_array to_array round-trip preserves all lane values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_alias_f32x4_1234()
val arr = v.to_array()
expect(arr[0]).to_equal(1.0)
expect(arr[1]).to_equal(2.0)
expect(arr[2]).to_equal(3.0)
expect(arr[3]).to_equal(4.0)
```

</details>

### SIMD back-compat alias wrappers — f64

#### A-04: vec4d_splat and vec4d_from_array work correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec4d_splat(2.718)
expect(v.lanes()).to_equal(4)
val arr_s = v.to_array()
expect(arr_s[0]).to_equal(2.718)

val v2 = make_alias_f64x4_1234()
val arr2 = v2.to_array()
expect(arr2[0]).to_equal(1.0)
expect(arr2[3]).to_equal(4.0)
```

</details>

### SIMD back-compat alias wrappers — i32

#### A-05: vec4i_splat produces 4-lane i32 vector; from_array round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec4i_splat(7)
expect(v.lanes()).to_equal(4)
val arr_s = v.to_array()
expect(arr_s[0]).to_equal(7)
expect(arr_s[3]).to_equal(7)

val v2 = make_alias_i32x4_5678()
val arr2 = v2.to_array()
expect(arr2[0]).to_equal(5)
expect(arr2[3]).to_equal(8)
```

</details>

### SIMD back-compat alias wrappers — u32

#### A-06: vec4u_splat produces 4-lane u32 vector; from_array round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec4u_splat(42)
expect(v.lanes()).to_equal(4)
val arr_s = v.to_array()
expect(arr_s[0]).to_equal(42)

val v2 = make_alias_u32x4_1234()
val arr2 = v2.to_array()
expect(arr2[0]).to_equal(1)
expect(arr2[3]).to_equal(4)
```

</details>

### SIMD type-alias declarations — parse smoke test

#### A-07: aliases.spl loads without parse error (type alias declarations are inert)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify function wrappers still work after type aliases were added above them.
# If the type declarations caused a parse error, this block would not execute.
val v = vec4f_splat(1.0)
val n = v.lanes()
expect(n).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/04_architecture/simd_unified_architecture_detail.md §11.3](doc/04_architecture/simd_unified_architecture_detail.md §11.3)


</details>
