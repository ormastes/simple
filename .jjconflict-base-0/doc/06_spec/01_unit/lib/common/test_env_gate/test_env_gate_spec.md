# Test Env Gate Specification

> Tests covering test_env_require, test_env_available, test_env_hardware_available, test_env_qemu_available, test_env_network_available, test_env_gate_reason.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Env Gate Specification

## Scenarios

### test_env_require

#### returns blocked: prefix when env var is not set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns blocked: prefix when env var is not set
   - Expected: result equals `blocked:SIMPLE_TEST_PROBE_GATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns blocked: prefix when env var is not set")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("blocked:SIMPLE_TEST_PROBE_GATE")
```

</details>

#### returns ready when env var is set to 1

- returns ready when env var is set to 1
   - Expected: result equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ready when env var is set to 1")
rt_env_set("SIMPLE_TEST_PROBE_GATE", "1")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("ready")
```

</details>

#### returns blocked when env var is set to 0

- returns blocked when env var is set to 0
   - Expected: result equals `blocked:SIMPLE_TEST_PROBE_GATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns blocked when env var is set to 0")
rt_env_set("SIMPLE_TEST_PROBE_GATE", "0")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("blocked:SIMPLE_TEST_PROBE_GATE")
```

</details>

#### blocked: prefix contains the env var name exactly

- blocked: prefix contains the env var name exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocked: prefix contains the env var name exactly")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_contain("SIMPLE_TEST_PROBE_GATE")
```

</details>

#### blocked: result starts with blocked:

- blocked: result starts with blocked:


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocked: result starts with blocked:")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_start_with("blocked:")
```

</details>

### test_env_available

#### returns false when env var is absent

- returns false when env var is absent
   - Expected: test_env_available("SIMPLE_TEST_PROBE_AVAIL") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when env var is absent")
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(test_env_available("SIMPLE_TEST_PROBE_AVAIL")).to_equal(false)
```

</details>

#### returns true when env var is set to 1

- returns true when env var is set to 1
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when env var is set to 1")
rt_env_set("SIMPLE_TEST_PROBE_AVAIL", "1")
val result = test_env_available("SIMPLE_TEST_PROBE_AVAIL")
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(result).to_equal(true)
```

</details>

#### returns false when env var is set to empty string

- returns false when env var is set to empty string
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when env var is set to empty string")
rt_env_set("SIMPLE_TEST_PROBE_AVAIL", "")
val result = test_env_available("SIMPLE_TEST_PROBE_AVAIL")
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(result).to_equal(false)
```

</details>

### test_env_hardware_available

#### returns false when SIMPLE_HW_TEST is not set to 1

- returns false when SIMPLE_HW_TEST is not set to 1
   - Expected: test_env_hardware_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when SIMPLE_HW_TEST is not set to 1")
rt_env_remove("SIMPLE_HW_TEST")
expect(test_env_hardware_available()).to_equal(false)
```

</details>

### test_env_qemu_available

#### returns false when SIMPLE_QEMU_TEST is not set to 1

- returns false when SIMPLE_QEMU_TEST is not set to 1
   - Expected: test_env_qemu_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when SIMPLE_QEMU_TEST is not set to 1")
rt_env_remove("SIMPLE_QEMU_TEST")
expect(test_env_qemu_available()).to_equal(false)
```

</details>

### test_env_network_available

#### returns false when SIMPLE_NET_TEST is not set to 1

- returns false when SIMPLE_NET_TEST is not set to 1
   - Expected: test_env_network_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when SIMPLE_NET_TEST is not set to 1")
rt_env_remove("SIMPLE_NET_TEST")
expect(test_env_network_available()).to_equal(false)
```

</details>

### test_env_gate_reason

#### contains the env var name in the reason

- contains the env var name in the reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the env var name in the reason")
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("SIMPLE_HW_TEST")
```

</details>

#### instructs the user to set the var to 1

- instructs the user to set the var to 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instructs the user to set the var to 1")
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("=1")
```

</details>

#### uses the correct env name for hardware gate

- uses the correct env name for hardware gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the correct env name for hardware gate")
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("SIMPLE_HW_TEST")
```

</details>

#### uses the correct env name for qemu gate

- uses the correct env name for qemu gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the correct env name for qemu gate")
val reason = test_env_gate_reason("SIMPLE_QEMU_TEST")
expect(reason).to_contain("SIMPLE_QEMU_TEST")
```

</details>

#### uses the correct env name for network gate

- uses the correct env name for network gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the correct env name for network gate")
val reason = test_env_gate_reason("SIMPLE_NET_TEST")
expect(reason).to_contain("SIMPLE_NET_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_env_require, test_env_available, test_env_hardware_available, test_env_qemu_available, test_env_network_available, test_env_gate_reason.
- test_env_require
- test_env_available
- test_env_hardware_available
- test_env_qemu_available
- test_env_network_available
- test_env_gate_reason

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `32c4b03e49735de792035ffd601fe964c64fb9c4de4aee88bc245663606931d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32c4b03e49735de792035ffd601fe964c64fb9c4de4aee88bc245663606931d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32c4b03e49735de792035ffd601fe964c64fb9c4de4aee88bc245663606931d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/test_env_gate/test_env_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/test_env_gate/test_env_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/test_env_gate/test_env_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns blocked: prefix when env var is not set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ready when env var is set to 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns blocked when env var is set to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
