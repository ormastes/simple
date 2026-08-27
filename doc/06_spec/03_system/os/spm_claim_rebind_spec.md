# Spm Claim Rebind Specification

> Tests covering FR-SPM-0003: SPM claim rebind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spm Claim Rebind Specification

## Scenarios

### FR-SPM-0003: SPM claim rebind

#### denies a task without the SPM claim privilege

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- denies a task without the SPM claim privilege
   - Expected: spm_claim_authorized(9201u64) is false
   - Expected: spm_claim_for_task(9201u64) equals `-1 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies a task without the SPM claim privilege")
spm_port_reset()
expect(spm_claim_authorized(9201u64)).to_equal(false)
expect(spm_claim_for_task(9201u64)).to_equal(-1 as i64)
```

</details>

#### authorizes an id.system mirror for the SPM claim path

- authorizes an id.system mirror for the SPM claim path
   - Expected: spm_claim_authorized(9202u64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("authorizes an id.system mirror for the SPM claim path")
bridge_set_mirror(9202u64, claim_mirror("id.system"))
expect(spm_claim_authorized(9202u64)).to_equal(true)
```

</details>

#### rebinds the boot placeholder to the real SPM task

- rebinds the boot placeholder to the real SPM task
   - Expected: spm_claim_for_task(9203u64) equals `0 as i64`
   - Expected: spm_port_registered_task() equals `9203u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rebinds the boot placeholder to the real SPM task")
spm_port_reset()
spm_port_register(SPM_PORT_WELL_KNOWN_TASK_ID)
bridge_set_mirror(9203u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9203u64)).to_equal(0 as i64)
expect(spm_port_registered_task()).to_equal(9203u64)
```

</details>

#### is idempotent for the same claimed SPM task

- is idempotent for the same claimed SPM task
   - Expected: spm_claim_for_task(9204u64) equals `0 as i64`
   - Expected: spm_claim_for_task(9204u64) equals `0 as i64`
   - Expected: spm_port_registered_task() equals `9204u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is idempotent for the same claimed SPM task")
spm_port_reset()
bridge_set_mirror(9204u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
expect(spm_port_registered_task()).to_equal(9204u64)
```

</details>

#### rejects a second real SPM task after claim

- rejects a second real SPM task after claim
   - Expected: spm_claim_for_task(9205u64) equals `0 as i64`
   - Expected: spm_claim_for_task(9206u64) equals `-2 as i64`
   - Expected: spm_port_registered_task() equals `9205u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a second real SPM task after claim")
spm_port_reset()
bridge_set_mirror(9205u64, claim_mirror("id.system"))
bridge_set_mirror(9206u64, claim_mirror("id.system"))
expect(spm_claim_for_task(9205u64)).to_equal(0 as i64)
expect(spm_claim_for_task(9206u64)).to_equal(-2 as i64)
expect(spm_port_registered_task()).to_equal(9205u64)
```

</details>

#### reserves syscall id 115 for SysSpmClaim

- reserves syscall id 115 for SysSpmClaim
   - Expected: syscall_id_spm_claim() equals `115u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reserves syscall id 115 for SysSpmClaim")
expect(syscall_id_spm_claim()).to_equal(115u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/spm_claim_rebind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-SPM-0003: SPM claim rebind.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `942b492ddc570163e177d2f81e784f11166092956ff4e83d5b6a251c84f30f45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `942b492ddc570163e177d2f81e784f11166092956ff4e83d5b6a251c84f30f45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `942b492ddc570163e177d2f81e784f11166092956ff4e83d5b6a251c84f30f45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/spm_claim_rebind_spec.spl
mirror: doc/06_spec/03_system/os/spm_claim_rebind_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/spm_claim_rebind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/spm_claim_rebind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/spm_claim_rebind_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a task without the SPM claim privilege' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/spm_claim_rebind_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'authorizes an id.system mirror for the SPM claim path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/spm_claim_rebind_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rebinds the boot placeholder to the real SPM task' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
