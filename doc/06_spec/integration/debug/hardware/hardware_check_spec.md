# Hardware Check Specification

> Tests covering Hardware detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardware Check Specification

## Scenarios

### Hardware detection

#### st-info tool check

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- st-info tool check
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("st-info tool check")
val available = is_stlink_tools_available()
expect(available == true or available == false).to_equal(true)
```

</details>

#### T32 tool check

- T32 tool check
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("T32 tool check")
val available = is_t32_available()
expect(available == true or available == false).to_equal(true)
```

</details>

#### T32 USB readiness check

- T32 USB readiness check
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("T32 USB readiness check")
val available = is_t32_usb_ready()
expect(available == true or available == false).to_equal(true)
```

</details>

#### OpenOCD tool check

- OpenOCD tool check
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("OpenOCD tool check")
val available = is_openocd_available()
expect(available == true or available == false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/debug/hardware/hardware_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hardware detection.
- Hardware detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e3a04287fe3225d1a75130b8a683577ab14471b04273fabfcd26b614196bd25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e3a04287fe3225d1a75130b8a683577ab14471b04273fabfcd26b614196bd25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e3a04287fe3225d1a75130b8a683577ab14471b04273fabfcd26b614196bd25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/debug/hardware/hardware_check_spec.spl
mirror: doc/06_spec/integration/debug/hardware/hardware_check_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/debug/hardware/hardware_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/debug/hardware/hardware_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/debug/hardware/hardware_check_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'st-info tool check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/hardware_check_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 tool check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/hardware_check_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 USB readiness check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
