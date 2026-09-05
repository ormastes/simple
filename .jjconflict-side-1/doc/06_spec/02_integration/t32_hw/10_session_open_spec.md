# 10 Session Open Specification

> <details>

<!-- sdn-diagram:id=10_session_open_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=10_session_open_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

10_session_open_spec -> std
10_session_open_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=10_session_open_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 10 Session Open Specification

## Scenarios

### T32 session open

#### connection state

#### opens session and stays connected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(client != nil).to_equal(true)
val ping = t32_hw_run_cmd(client, "PING")
match ping:
    Ok(_): expect("ping ok").to_contain("ok")
    Err(e): expect("ping failed: {e}").to_equal("")
```

</details>

#### session has correct host

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(client.host).to_equal(t32_hw_host())
```

</details>

#### session has correct port

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(client.port).to_equal(t32_hw_port())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/10_session_open_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 session open

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
