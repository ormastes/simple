# Wine Vm Gate Specification

> Tests covering Wine VM readiness gate, feature coverage, fault evidence, container evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Vm Gate Specification

## Scenarios

### Wine VM readiness gate

### feature coverage

#### lists Wine-level VM and namespace requirements

- lists Wine-level VM and namespace requirements
   - Expected: required[0] equals `reserve`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists Wine-level VM and namespace requirements")
val required = wine_vm_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("reserve")
```

</details>

#### reports the first missing VM primitive

- reports the first missing VM primitive
   - Expected: state equals `missing-mprotect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing VM primitive")
val state = wine_vm_gate("reserve commit unmap fixed-map")
expect(state).to_equal("missing-mprotect")
```

</details>

#### returns ready when VM and namespace requirements are present

- returns ready when VM and namespace requirements are present
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ready when VM and namespace requirements are present")
val state = wine_vm_gate("reserve commit unmap fixed-map mprotect exec-perm guard-page page-fault stack-growth user-pointer pid-namespace fs-namespace ipc-namespace net-namespace cap-namespace")
expect(state).to_equal("ready")
```

</details>

### fault evidence

#### requires process, thread, address, access, and policy fields

- requires process, thread, address, access, and policy fields
   - Expected: state equals `missing-policy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires process, thread, address, access, and policy fields")
val state = wine_vm_fault_gate("process thread address access")
expect(state).to_equal("missing-policy")
```

</details>

### container evidence

#### requires pid, filesystem, IPC, network, and capability namespaces

- requires pid, filesystem, IPC, network, and capability namespaces
   - Expected: state equals `missing-capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires pid, filesystem, IPC, network, and capability namespaces")
val state = wine_container_gate("pid fs ipc net")
expect(state).to_equal("missing-capability")
```

</details>

#### does not accept namespace substrings as container evidence

- does not accept namespace substrings as container evidence
   - Expected: wine_container_gate("stupid fs ipc net capability") equals `missing-pid`
   - Expected: wine_container_gate("pid xfs ipc net capability") equals `missing-fs`
   - Expected: wine_container_gate("pid fs epic net capability") equals `missing-ipc`
   - Expected: wine_container_gate("pid fs ipc ethernet capability") equals `missing-net`
   - Expected: wine_container_gate("pid fs ipc net incapability") equals `missing-capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not accept namespace substrings as container evidence")
expect(wine_container_gate("stupid fs ipc net capability")).to_equal("missing-pid")
expect(wine_container_gate("pid xfs ipc net capability")).to_equal("missing-fs")
expect(wine_container_gate("pid fs epic net capability")).to_equal("missing-ipc")
expect(wine_container_gate("pid fs ipc ethernet capability")).to_equal("missing-net")
expect(wine_container_gate("pid fs ipc net incapability")).to_equal("missing-capability")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_vm_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine VM readiness gate, feature coverage, fault evidence, container evidence.
- Wine VM readiness gate
- feature coverage
- fault evidence
- container evidence

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b296b772f215daf0760985b192aa96a00ed714d0f833d919d52ede72779a129`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b296b772f215daf0760985b192aa96a00ed714d0f833d919d52ede72779a129`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b296b772f215daf0760985b192aa96a00ed714d0f833d919d52ede72779a129`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_vm_gate_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_vm_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_vm_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_vm_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_vm_gate_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists Wine-level VM and namespace requirements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_vm_gate_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing VM primitive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_vm_gate_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ready when VM and namespace requirements are present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
