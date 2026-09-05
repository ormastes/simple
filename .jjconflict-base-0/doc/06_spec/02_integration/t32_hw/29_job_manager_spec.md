# 29 Job Manager Specification

> 1. Ok

<!-- sdn-diagram:id=29_job_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=29_job_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

29_job_manager_spec -> std
29_job_manager_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=29_job_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 29 Job Manager Specification

## Scenarios

### T32 job manager

#### synchronous eval

#### eval completes synchronously

1. Ok
2. Err
   - Expected: "eval 1+1 failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "1+1")
match result:
    Ok(v):
        # Should return a value immediately
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval 1+1 failed: {e}").to_equal("")
```

</details>

#### long eval completes

1. Ok
2. Err
   - Expected: "VERSION.BUILD() failed: {e}" equals ``


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
        expect("VERSION.BUILD() failed: {e}").to_equal("")
```

</details>

#### sequential evals

#### multiple evals in sequence

1. Ok
2. Err
3. Ok
4. Err
5. Ok
6. Err
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = t32_hw_eval(client, "1+1")
val r2 = t32_hw_eval(client, "2+2")
val r3 = t32_hw_eval(client, "3+3")
val ok1 = match r1:
    Ok(_): true
    Err(_): false
val ok2 = match r2:
    Ok(_): true
    Err(_): false
val ok3 = match r3:
    Ok(_): true
    Err(_): false
val all_ok = ok1 and ok2 and ok3
expect(all_ok).to_equal(true)
```

</details>

#### error recovery

#### eval after error recovers

1. Ok
2. Err
   - Expected: "recovery eval failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Send a bad expression first
val bad = t32_hw_eval(client, "ZZZNOTEXPR.ZZZZ()")
# bad may be Ok or Err depending on T32 behavior
# Now send a good expression and verify it works
val good = t32_hw_eval(client, "VERSION.BUILD()")
match good:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("recovery eval failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/29_job_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 job manager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
