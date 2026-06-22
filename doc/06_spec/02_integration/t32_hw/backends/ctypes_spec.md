# T32 Backend: C API (ctypes)

> Tests core T32 operations using the C API via ctypes/dlopen.

<!-- sdn-diagram:id=ctypes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ctypes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ctypes_spec -> std
ctypes_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ctypes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Backend: C API (ctypes)

Tests core T32 operations using the C API via ctypes/dlopen.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/backends/ctypes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests core T32 operations using the C API via ctypes/dlopen.
Requires compiled mode (spl_dlopen is not available in interpreter).
Requires t32api64.so library.

## Scenarios

### T32 via ctypes backend

#### when C API library is available

#### t32api64.so exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    expect("ctypes not available").to_contain("not available")
    return
expect(t32_hw_ctypes_available()).to_equal(true)
```

</details>

#### connects and pings

1. shared test connect and ping


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_connect_and_ping()
```

</details>

#### evaluates VERSION.BUILD()

1. shared test eval version


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_eval_version()
```

</details>

#### runs PRACTICE command

1. shared test cmd run


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_cmd_run()
```

</details>

#### queries STATE.RUN()

1. shared test state query


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_state_query()
```

</details>

#### reads PC register

1. shared test register read


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_register_read()
```

</details>

#### halt-step-halt cycle

1. shared test step and halt


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_step_and_halt()
```

</details>

#### recovers from error

1. shared test error recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_ctypes_available():
    return
shared_test_error_recovery()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
