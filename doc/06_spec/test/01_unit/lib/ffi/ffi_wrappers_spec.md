# FFI Wrappers Unit Tests

> 1. check

<!-- sdn-diagram:id=ffi_wrappers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_wrappers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_wrappers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_wrappers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FFI Wrappers Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-FFI-002 |
| Category | Lib \| FFI \| Wrappers |
| Status | Implemented |
| Source | `test/01_unit/lib/ffi/ffi_wrappers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### File System FFI

#### file_exists wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_file_exists"
check(fn_name.starts_with("rt_"))
```

</details>

#### file_read_text wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_file_read_text"
check(fn_name.contains("read"))
```

</details>

#### file_write_text wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_file_write_text"
check(fn_name.contains("write"))
```

</details>

#### file_delete wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_file_delete"
check(fn_name.contains("delete"))
```

</details>

#### dir_create wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_dir_create"
check(fn_name.contains("dir"))
```

</details>

#### dir_list wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_dir_list"
check(fn_name.contains("list"))
```

</details>

### Process FFI

#### process_exec wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_process_exec"
check(fn_name.contains("process"))
```

</details>

#### process_output wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_process_output"
check(fn_name.contains("output"))
```

</details>

#### env_get wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_env_get"
check(fn_name.contains("env"))
```

</details>

#### env_set wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_env_set"
check(fn_name.contains("env"))
```

</details>

### Network FFI

#### tcp_connect wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_tcp_connect"
check(fn_name.contains("tcp"))
```

</details>

#### tcp_listen wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_tcp_listen"
check(fn_name.contains("listen"))
```

</details>

#### http_get wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_http_get"
check(fn_name.contains("http"))
```

</details>

#### http_post wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_http_post"
check(fn_name.contains("post"))
```

</details>

### Time FFI

#### time_now wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_time_now_ms"
check(fn_name.contains("time"))
```

</details>

#### sleep wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_sleep_ms"
check(fn_name.contains("sleep"))
```

</details>

### Memory FFI

#### alloc wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_alloc"
check(fn_name.contains("alloc"))
```

</details>

#### free wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_free"
check(fn_name.contains("free"))
```

</details>

#### realloc wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_realloc"
check(fn_name.contains("realloc"))
```

</details>

#### memcpy wrapper

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "rt_memcpy"
check(fn_name.contains("memcpy"))
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
