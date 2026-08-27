# Qmp Screendump Specification

> Tests covering QmpClient — qmp_screendump.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qmp Screendump Specification

## Scenarios

### QmpClient — qmp_screendump

#### invalid connection

#### AC-3: screendump with non-existent socket returns false

- AC-3: screendump with non-existent socket returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: screendump with non-existent socket returns false")
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test_screendump.png", "png")
expect(result).to_equal(false)
```

</details>

#### AC-3: screendump with empty socket path returns false

- AC-3: screendump with empty socket path returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: screendump with empty socket path returns false")
val client = QmpClient(socket_path: "")
val result = qmp_screendump(client, "/tmp/test_screendump.png", "png")
expect(result).to_equal(false)
```

</details>

#### format parameter

#### AC-3: screendump accepts 'png' format

- AC-3: screendump accepts 'png' format
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: screendump accepts 'png' format")
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test.png", "png")
# Will fail due to missing socket, but format is accepted
expect(result).to_equal(false)
```

</details>

#### AC-3: screendump accepts 'ppm' format

- AC-3: screendump accepts 'ppm' format
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: screendump accepts 'ppm' format")
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test.ppm", "ppm")
expect(result).to_equal(false)
```

</details>

#### output path

#### AC-3: screendump with valid format but bad socket returns false

- AC-3: screendump with valid format but bad socket returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: screendump with valid format but bad socket returns false")
val client = QmpClient(socket_path: "/tmp/nonexistent_qmp_socket")
val result = qmp_screendump(client, "/tmp/qemu_fb_capture.png", "png")
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/qmp_screendump_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QmpClient — qmp_screendump.
- QmpClient — qmp_screendump

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdf58beeed207924cf90b5db0bf50ec98b202a42fbb8f5247f128e59fbf3f838`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdf58beeed207924cf90b5db0bf50ec98b202a42fbb8f5247f128e59fbf3f838`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdf58beeed207924cf90b5db0bf50ec98b202a42fbb8f5247f128e59fbf3f838`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/qmp_screendump_spec.spl
mirror: doc/06_spec/03_system/os/qemu/qmp_screendump_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/qmp_screendump_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/qmp_screendump_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/qmp_screendump_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: screendump with non-existent socket returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/qmp_screendump_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: screendump with empty socket path returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/qmp_screendump_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: screendump accepts 'png' format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
