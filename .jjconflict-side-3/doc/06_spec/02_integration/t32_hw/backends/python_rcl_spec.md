# T32 Backend: Python RCL Bridge

> Tests core T32 operations using the Python RCL bridge backend.

<!-- sdn-diagram:id=python_rcl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=python_rcl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

python_rcl_spec -> std
python_rcl_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=python_rcl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Backend: Python RCL Bridge

Tests core T32 operations using the Python RCL bridge backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/backends/python_rcl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests core T32 operations using the Python RCL bridge backend.
Requires python3 and lauterbach.trace32.rcl package.

## Scenarios

### T32 via Python RCL backend

#### when Python RCL is available

#### python binary exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available():
    expect("python not available").to_contain("not available")
    return
if not t32_hw_has_software_build():
    expect("SOFTWARE.BUILD not available in this T32 version -- Python RCL requires newer T32").to_contain("not available")
    return
expect(t32_hw_python_available()).to_equal(true)
```

</details>

#### connects and pings

1. shared test connect and ping


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_connect_and_ping()
```

</details>

#### evaluates VERSION.BUILD()

1. shared test eval version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_eval_version()
```

</details>

#### runs PRACTICE command

1. shared test cmd run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_cmd_run()
```

</details>

#### queries STATE.RUN()

1. shared test state query


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_state_query()
```

</details>

#### reads PC register

1. shared test register read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_register_read()
```

</details>

#### halt-step-halt cycle

1. shared test step and halt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_step_and_halt()
```

</details>

#### recovers from error

1. shared test error recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
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
