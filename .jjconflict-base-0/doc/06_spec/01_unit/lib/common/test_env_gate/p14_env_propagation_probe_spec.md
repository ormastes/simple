# P14 Env Propagation Probe Specification

> Tests covering P14 external env propagation reaches the spec body.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P14 Env Propagation Probe Specification

## Scenarios

### P14 external env propagation reaches the spec body

#### propagates the probe variable itself

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- propagates the probe variable itself
   - Expected: observed("SIMPLE_P14_PROBE") equals `expected("SIMPLE_P14_PROBE")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates the probe variable itself")
expect(observed("SIMPLE_P14_PROBE")).to_equal(expected("SIMPLE_P14_PROBE"))
```

</details>

#### propagates SIMPLE_HW_TEST

- propagates SIMPLE_HW_TEST
   - Expected: observed("SIMPLE_HW_TEST") equals `expected("SIMPLE_HW_TEST")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SIMPLE_HW_TEST")
expect(observed("SIMPLE_HW_TEST")).to_equal(expected("SIMPLE_HW_TEST"))
```

</details>

#### propagates SIMPLE_QEMU_TEST

- propagates SIMPLE_QEMU_TEST
   - Expected: observed("SIMPLE_QEMU_TEST") equals `expected("SIMPLE_QEMU_TEST")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SIMPLE_QEMU_TEST")
expect(observed("SIMPLE_QEMU_TEST")).to_equal(expected("SIMPLE_QEMU_TEST"))
```

</details>

#### propagates SIMPLE_NET_TEST

- propagates SIMPLE_NET_TEST
   - Expected: observed("SIMPLE_NET_TEST") equals `expected("SIMPLE_NET_TEST")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SIMPLE_NET_TEST")
expect(observed("SIMPLE_NET_TEST")).to_equal(expected("SIMPLE_NET_TEST"))
```

</details>

#### propagates SIMPLE_GPU_TEST

- propagates SIMPLE_GPU_TEST
   - Expected: observed("SIMPLE_GPU_TEST") equals `expected("SIMPLE_GPU_TEST")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SIMPLE_GPU_TEST")
expect(observed("SIMPLE_GPU_TEST")).to_equal(expected("SIMPLE_GPU_TEST"))
```

</details>

#### propagates SIMPLE_LLVM_TEST

- propagates SIMPLE_LLVM_TEST
   - Expected: observed("SIMPLE_LLVM_TEST") equals `expected("SIMPLE_LLVM_TEST")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SIMPLE_LLVM_TEST")
expect(observed("SIMPLE_LLVM_TEST")).to_equal(expected("SIMPLE_LLVM_TEST"))
```

</details>

#### test_env_available agrees with the raw read for SIMPLE_HW_TEST

- test_env_available agrees with the raw read for SIMPLE_HW_TEST
   - Expected: test_env_available("SIMPLE_HW_TEST") equals `want`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_env_available agrees with the raw read for SIMPLE_HW_TEST")
val want = rt_env_get("SIMPLE_P14_PROBE") != nil
expect(test_env_available("SIMPLE_HW_TEST")).to_equal(want)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering P14 external env propagation reaches the spec body.
- P14 external env propagation reaches the spec body

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `0ccdb5dfdd6061f1b364bd661705aa72a5863e9da6241781c77812c5448ea2bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ccdb5dfdd6061f1b364bd661705aa72a5863e9da6241781c77812c5448ea2bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ccdb5dfdd6061f1b364bd661705aa72a5863e9da6241781c77812c5448ea2bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates the probe variable itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates SIMPLE_HW_TEST' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates SIMPLE_QEMU_TEST' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
