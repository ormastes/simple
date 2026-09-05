# Spm Claim Rebind Specification

> 1. spm port reset

<!-- sdn-diagram:id=spm_claim_rebind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spm_claim_rebind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spm_claim_rebind_spec -> std
spm_claim_rebind_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spm_claim_rebind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spm Claim Rebind Specification

## Scenarios

### FR-SPM-0003: SPM claim rebind

#### denies a task without the SPM claim privilege

1. spm port reset
   - Expected: spm_claim_authorized(9201u64) is false
   - Expected: spm_claim_for_task(9201u64) equals `-1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
expect(spm_claim_authorized(9201u64)).to_equal(false)
expect(spm_claim_for_task(9201u64)).to_equal(-1 as i64)
```

</details>

#### authorizes an id.system mirror for the SPM claim path

1. bridge set mirror
   - Expected: spm_claim_authorized(9202u64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bridge_set_mirror(9202u64, claim_mirror("id.system"))
expect(spm_claim_authorized(9202u64)).to_equal(true)
```

</details>

#### rebinds the boot placeholder to the real SPM task

1. spm port reset
2. spm port register
3. bridge set mirror
   - Expected: spm_claim_for_task(9203u64) equals `0 as i64`
   - Expected: spm_port_registered_task() equals `9203u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(SPM_PORT_WELL_KNOWN_TASK_ID)
bridge_set_mirror(9203u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9203u64)).to_equal(0 as i64)
expect(spm_port_registered_task()).to_equal(9203u64)
```

</details>

#### is idempotent for the same claimed SPM task

1. spm port reset
2. bridge set mirror
   - Expected: spm_claim_for_task(9204u64) equals `0 as i64`
   - Expected: spm_claim_for_task(9204u64) equals `0 as i64`
   - Expected: spm_port_registered_task() equals `9204u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
bridge_set_mirror(9204u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
expect(spm_port_registered_task()).to_equal(9204u64)
```

</details>

#### rejects a second real SPM task after claim

1. spm port reset
2. bridge set mirror
3. bridge set mirror
   - Expected: spm_claim_for_task(9205u64) equals `0 as i64`
   - Expected: spm_claim_for_task(9206u64) equals `-2 as i64`
   - Expected: spm_port_registered_task() equals `9205u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
bridge_set_mirror(9205u64, claim_mirror("id.system"))
bridge_set_mirror(9206u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9205u64)).to_equal(0 as i64)
expect(spm_claim_for_task(9206u64)).to_equal(-2 as i64)
expect(spm_port_registered_task()).to_equal(9205u64)
```

</details>

#### reserves syscall id 115 for SysSpmClaim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(syscall_id_spm_claim()).to_equal(115u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/spm_claim_rebind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-SPM-0003: SPM claim rebind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
