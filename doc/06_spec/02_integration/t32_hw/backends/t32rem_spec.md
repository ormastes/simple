# T32 Backend: t32rem CLI

> Tests core T32 operations using the t32rem CLI backend.

<!-- sdn-diagram:id=t32rem_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32rem_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32rem_spec -> std
t32rem_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32rem_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Backend: t32rem CLI

Tests core T32 operations using the t32rem CLI backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/backends/t32rem_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests core T32 operations using the t32rem CLI backend.

## Scenarios

### T32 via t32rem backend

#### when t32rem is available

#### t32rem binary exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_hw_t32rem_available()).to_equal(true)
```

</details>

#### connects and pings

1. shared test connect and ping


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_connect_and_ping()
```

</details>

#### evaluates VERSION.BUILD()

1. shared test eval version


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_eval_version()
```

</details>

#### runs PRACTICE command

1. shared test cmd run


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_cmd_run()
```

</details>

#### queries STATE.RUN()

1. shared test state query


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_state_query()
```

</details>

#### reads PC register

1. shared test register read


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_register_read()
```

</details>

#### halt-step-halt cycle

1. shared test step and halt


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_test_step_and_halt()
```

</details>

#### recovers from error

1. shared test error recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
