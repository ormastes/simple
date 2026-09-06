# lsusb PCI Class Filter Specification

> Verifies that `is_usb_controller` correctly identifies USB host controllers by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsusb PCI Class Filter Specification

Verifies that `is_usb_controller` correctly identifies USB host controllers by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/unit/os/tools/dev/lsusb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `is_usb_controller` correctly identifies USB host controllers
by PCI class 0x0C and subclass 0x03, and rejects other class/subclass pairs.

## Scenarios

### is_usb_controller PCI class filter

#### accepts class 0x0C subclass 0x03 as a USB controller

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts class 0x0C subclass 0x03 as a USB controller
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts class 0x0C subclass 0x03 as a USB controller")
val result = is_usb_controller(0x0C, 0x03)
expect(result).to_equal(true)
```

</details>

#### rejects class 0x01 (mass storage) as not USB

- rejects class 0x01 (mass storage) as not USB
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects class 0x01 (mass storage) as not USB")
val result = is_usb_controller(0x01, 0x06)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x0C with wrong subclass as not USB

- rejects class 0x0C with wrong subclass as not USB
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects class 0x0C with wrong subclass as not USB")
val result = is_usb_controller(0x0C, 0x00)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x02 (network) as not USB

- rejects class 0x02 (network) as not USB
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects class 0x02 (network) as not USB")
val result = is_usb_controller(0x02, 0x00)
expect(result).to_equal(false)
```

</details>

#### rejects class 0x03 (display) as not USB

- rejects class 0x03 (display) as not USB
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects class 0x03 (display) as not USB")
val result = is_usb_controller(0x03, 0x00)
expect(result).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `5649ada5b02d4c55b098de0975cc9768cb180ebf08829f90128104d44cfa1933`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5649ada5b02d4c55b098de0975cc9768cb180ebf08829f90128104d44cfa1933`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5649ada5b02d4c55b098de0975cc9768cb180ebf08829f90128104d44cfa1933`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tools/dev/lsusb_spec.spl
mirror: doc/06_spec/unit/os/tools/dev/lsusb_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tools/dev/lsusb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tools/dev/lsusb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tools/dev/lsusb_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts class 0x0C subclass 0x03 as a USB controller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/dev/lsusb_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects class 0x01 (mass storage) as not USB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/dev/lsusb_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects class 0x0C with wrong subclass as not USB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
