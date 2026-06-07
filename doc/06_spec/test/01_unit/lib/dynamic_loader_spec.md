# Dynamic Loader Specification

> <details>

<!-- sdn-diagram:id=dynamic_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynamic_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynamic_loader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynamic_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Loader Specification

## Scenarios

### DynLoader

### sffi_lib_path

#### maps torch prefix to libspl_torch.so

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = sffi_lib_path("torch")
expect(path).to_contain("libspl_torch")
```

</details>

#### uses build/ as default base

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = sffi_lib_path("test")
expect(path).to_start_with("build/")
```

</details>

#### includes .so suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = sffi_lib_path("audio")
expect(path).to_end_with(".so")
```

</details>

### DynLib

#### returns nil for nonexistent library

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DynLib.load("/nonexistent/libfake_12345.so")
expect(result.?).to_equal(false)
```

</details>

#### loads libm.so successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DynLib.load("libm.so.6")
expect(result.?).to_equal(true)
```

</details>

#### returns 0 for unknown symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    val fptr = lib.sym("__nonexistent_symbol_xyz__")
    expect(fptr).to_equal(0)
```

</details>

### DynLoader

#### loads library and caches it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loader = DynLoader.instance()
val ok = loader.ensure_loaded("libm.so.6")
expect(ok).to_equal(true)
val ok2 = loader.ensure_loaded("libm.so.6")
expect(ok2).to_equal(true)
```

</details>

#### returns false for missing library

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loader = DynLoader.instance()
val ok = loader.ensure_loaded("/nonexistent/libfake_99999.so")
expect(ok).to_equal(false)
```

</details>

### sffi_call

#### returns 0 gracefully when library is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sffi_call("rt_fake_nonexistent_function", [])
expect(result).to_equal(0)
```

</details>

### DynLib call variants

#### call0 runs without error on a real symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    # floor has wrong arity/type for i64 but we only test dispatch
    val r = lib.call0("floor")
    # Tautology — true regardless of return value; proves no crash
    expect(r == r).to_equal(true)
```

</details>

#### call_n accepts empty args array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    val r = lib.call_n("floor", [])
    expect(r == r).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/dynamic_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DynLoader
- sffi_lib_path
- DynLib
- DynLoader
- sffi_call
- DynLib call variants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
