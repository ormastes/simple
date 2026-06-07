# Spm Priv Check Task Mirror Specification

> 1. bridge set mirror

<!-- sdn-diagram:id=spm_priv_check_task_mirror_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spm_priv_check_task_mirror_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spm_priv_check_task_mirror_spec -> std
spm_priv_check_task_mirror_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spm_priv_check_task_mirror_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spm Priv Check Task Mirror Specification

## Scenarios

### FR-SPM-0002 sys_priv_check task mirror lookup

#### caller task routing

#### allows the caller whose mirror covers the requested id path

1. bridge set mirror
   - Expected: spm_priv_check_for_task(9101u64, "id.user.banking".bytes()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bridge_set_mirror(9101u64, mirror("id.user", 1u8))
expect(spm_priv_check_for_task(9101u64, "id.user.banking".bytes())).to_equal(true)
```

</details>

#### denies a different caller with a mismatched mirror

1. bridge set mirror
   - Expected: spm_priv_check_for_task(9102u64, "id.user.banking".bytes()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bridge_set_mirror(9102u64, mirror("id.admin", 1u8))
expect(spm_priv_check_for_task(9102u64, "id.user.banking".bytes())).to_equal(false)
```

</details>

#### denies callers without mirrors and empty id paths

1. bridge set mirror
   - Expected: spm_priv_check_for_task(9103u64, []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(spm_priv_check_for_task(9199u64, "id.user.banking".bytes())).to_equal(false)
bridge_set_mirror(9103u64, mirror("id.user", 1u8))
expect(spm_priv_check_for_task(9103u64, [])).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/spm_priv_check_task_mirror_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-SPM-0002 sys_priv_check task mirror lookup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
