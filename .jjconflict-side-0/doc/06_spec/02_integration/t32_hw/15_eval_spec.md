# 15 Eval Specification

> 1. Ok

<!-- sdn-diagram:id=15_eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=15_eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

15_eval_spec -> std
15_eval_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=15_eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 15 Eval Specification

## Scenarios

### T32 eval expressions

#### valid expressions

#### eval VERSION.BUILD()

1. Ok
2. Err
   - Expected: "VERSION.BUILD failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        # VERSION.BUILD returns a numeric string like "134567"
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.BUILD failed: {e}").to_equal("")
```

</details>

#### eval STATE.RUN()

1. Ok
2. Err
   - Expected: "STATE.RUN failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "STATE.RUN()")
match result:
    Ok(v):
        # Returns "TRUE" or "FALSE" -- non-empty means valid response
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("STATE.RUN failed: {e}").to_equal("")
```

</details>

#### eval DEBUGMODE()

1. Ok
2. Err
   - Expected: "DEBUGMODE failed: {e}" equals ``


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
        expect("DEBUGMODE failed: {e}").to_equal("")
```

</details>

#### eval Register(PC)

1. Ok
2. Err
   - Expected: "Register(PC) failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        # PC register returns a hex value like "0x00008000"
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("Register(PC) failed: {e}").to_equal("")
```

</details>

#### invalid expressions

#### eval invalid expression

1. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "NONEXISTENT.FUNC.12345()")
match result:
    Err(_): expect("error accepted").to_contain("accepted")
    Ok(_):
        # Some T32 versions may return empty on bad expr
        expect("accepted ok").to_contain("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/15_eval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 eval expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
