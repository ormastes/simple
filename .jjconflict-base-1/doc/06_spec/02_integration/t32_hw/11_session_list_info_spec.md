# 11 Session List Info Specification

> <details>

<!-- sdn-diagram:id=11_session_list_info_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=11_session_list_info_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

11_session_list_info_spec -> std
11_session_list_info_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=11_session_list_info_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 11 Session List Info Specification

## Scenarios

### T32 session list info

#### session responsiveness

#### session responds after open

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ping = t32_hw_run_cmd(client, "PING")
match ping:
    Ok(_): expect("ping ok").to_contain("ok")
    Err(e): expect("PING failed: {e}").to_equal("")
```

</details>

#### eval works on open session

1. Ok
2. Err
   - Expected: "eval failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval failed: {e}").to_equal("")
```

</details>

#### can query system mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("SYStem.MODE failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/11_session_list_info_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 session list info

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
