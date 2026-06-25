# 25 Status Snapshot Specification

> 1. Ok

<!-- sdn-diagram:id=25_status_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=25_status_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

25_status_snapshot_spec -> std
25_status_snapshot_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=25_status_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 25 Status Snapshot Specification

## Scenarios

### T32 status snapshot

#### individual status fields

#### STATE.RUN() returns boolean

1. Ok
   - Expected: valid is true
2. Err
   - Expected: "STATE.RUN() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "STATE.RUN()")
match result:
    Ok(v):
        val valid = v.contains("TRUE") or v.contains("FALSE")
        expect(valid).to_equal(true)
    Err(e):
        expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### STATE.TARGET() returns target info

1. Ok
2. Err
   - Expected: "STATE.TARGET() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "STATE.TARGET()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("STATE.TARGET() failed: {e}").to_equal("")
```

</details>

#### DEBUGMODE() returns mode

1. Ok
2. Err
   - Expected: "DEBUGMODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "DEBUGMODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("DEBUGMODE() failed: {e}").to_equal("")
```

</details>

#### SYStem.MODE() returns system mode

1. Ok
2. Err
   - Expected: "SYStem.MODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("SYStem.MODE() failed: {e}").to_equal("")
```

</details>

#### consistency

#### status fields are consistent

1. Ok
2. Err
3. Ok
4. Err
5. Ok
6. Err
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Read multiple status fields and confirm they all succeed
val run_result = t32_hw_eval(client, "STATE.RUN()")
val target_result = t32_hw_eval(client, "STATE.TARGET()")
val mode_result = t32_hw_eval(client, "SYStem.MODE()")
val run_ok = match run_result:
    Ok(_): true
    Err(_): false
val target_ok = match target_result:
    Ok(_): true
    Err(_): false
val mode_ok = match mode_result:
    Ok(_): true
    Err(_): false
val all_ok = run_ok and target_ok and mode_ok
expect(all_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/25_status_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 status snapshot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
