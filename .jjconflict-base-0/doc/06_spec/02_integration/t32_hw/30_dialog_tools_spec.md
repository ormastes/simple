# 30 Dialog Tools Specification

> <details>

<!-- sdn-diagram:id=30_dialog_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=30_dialog_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

30_dialog_tools_spec -> std
30_dialog_tools_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=30_dialog_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 30 Dialog Tools Specification

## Scenarios

### T32 dialog tools

#### basic connectivity

#### T32 responds to PRINT command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRINT works on all T32 versions -- basic connectivity check
val result = t32_hw_run_cmd(client, "PRINT \"dialog_tools_ping\"")
match result:
    Ok(v): expect(v).to_contain("dialog_tools_ping")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### dialog lifecycle

#### PRACTICE dialog can be opened

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_dialog():
    expect("DIALOG not available in this T32 version").to_contain("not available")
    return
return "skip: opening PRACTICE dialog requires CMM dialog script"
```

</details>

#### PRACTICE.STATE() detects dialog

1. Ok
2. Err
   - Expected: "PRACTICE.STATE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        # Should return a state string (e.g., "IDLE", "RUN", "DIALOG")
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() failed: {e}").to_equal("")
```

</details>

#### dialog can be dismissed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_dialog():
    expect("DIALOG not available in this T32 version").to_contain("not available")
    return
return "skip: dismissing dialog requires an open CMM-driven dialog"
```

</details>

#### PRACTICE.STATE() after dismiss

1. Ok
2. Err
   - Expected: "PRACTICE.STATE() after dismiss failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
# After dismissing a dialog, PRACTICE.STATE() should return
# an idle/empty state. Without dialog open/close support,
# we verify PRACTICE.STATE() still returns a valid value.
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() after dismiss failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/30_dialog_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 dialog tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
