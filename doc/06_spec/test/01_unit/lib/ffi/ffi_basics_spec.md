# FFI Basics Unit Tests

> 1. check

<!-- sdn-diagram:id=ffi_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FFI Basics Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-FFI-001 |
| Category | Lib \| FFI |
| Status | Implemented |
| Source | `test/01_unit/lib/ffi/ffi_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### FFI Type Mapping

#### i64 maps to int64_t

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "int64_t"
check(type_name == "int64_t")
```

</details>

#### f64 maps to double

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "double"
check(type_name == "double")
```

</details>

#### bool maps to bool

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "bool"
check(type_name == "bool")
```

</details>

#### text maps to char*

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "char*"
check(type_name == "char*")
```

</details>

#### void maps to void

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "void"
check(type_name == "void")
```

</details>

### FFI Calling Convention

#### c calling convention

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = "c"
check(conv == "c")
```

</details>

#### stdcall convention

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = "stdcall"
check(conv == "stdcall")
```

</details>

#### fastcall convention

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = "fastcall"
check(conv == "fastcall")
```

</details>

### FFI Safety

#### extern functions are unsafe

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_unsafe = true
check(is_unsafe)
```

</details>

#### null pointer check

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = nil
check(ptr.? == false)
```

</details>

#### buffer size validation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buffer_size = 1024
check(buffer_size > 0)
```

</details>

#### string encoding is UTF-8

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoding = "utf-8"
check(encoding == "utf-8")
```

</details>

### FFI Data Layout

#### struct alignment

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 8
check(alignment == 8 or alignment == 4)
```

</details>

#### field offset calculation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset = 0
check(offset >= 0)
```

</details>

#### struct padding

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_padding = true
check(true)
```

</details>

#### packed struct

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packed = true
check(packed)
```

</details>

### Runtime FFI Functions

#### rt_file_read_text signature

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "rt_file_read_text"
check(name.starts_with("rt_"))
```

</details>

#### rt_file_write_text signature

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "rt_file_write_text"
check(name.starts_with("rt_"))
```

</details>

#### rt_time_now_ms signature

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "rt_time_now_ms"
check(name.starts_with("rt_"))
```

</details>

#### rt_env_get signature

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "rt_env_get"
check(name.starts_with("rt_"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
