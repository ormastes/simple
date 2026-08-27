# Collection Algorithm QEMU Tests

> Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap, and RingBuffer logic via semihost output. Tests that bare-metal collection implementations work correctly without heap allocation on emulated hardware.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Algorithm QEMU Tests

Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap, and RingBuffer logic via semihost output. Tests that bare-metal collection implementations work correctly without heap allocation on emulated hardware.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/collections_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap,
and RingBuffer logic via semihost output. Tests that bare-metal collection
implementations work correctly without heap allocation on emulated hardware.

## Scenarios

### Collection QEMU Tests

<details>
<summary>Advanced: FixedArray push/pop order is correct</summary>

#### FixedArray push/pop order is correct _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FixedArray push/pop order is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FixedArray push/pop order is correct")
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: FixedMap hash/put/get is correct</summary>

#### FixedMap hash/put/get is correct _(slow)_

- FixedMap hash/put/get is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FixedMap hash/put/get is correct")
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: RingBuffer enqueue/dequeue with wrap-around is correct</summary>

#### RingBuffer enqueue/dequeue with wrap-around is correct _(slow)_

- RingBuffer enqueue/dequeue with wrap-around is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RingBuffer enqueue/dequeue with wrap-around is correct")
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: all collection tests complete</summary>

#### all collection tests complete _(slow)_

- all collection tests complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all collection tests complete")
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("=== Collection Tests Complete ===")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `eb7aa5a8a71b90e3f0dcdc9dff074cb54079e19f59267718b57bbff0ef4ee0fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb7aa5a8a71b90e3f0dcdc9dff074cb54079e19f59267718b57bbff0ef4ee0fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb7aa5a8a71b90e3f0dcdc9dff074cb54079e19f59267718b57bbff0ef4ee0fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/baremetal/collections_qemu_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/collections_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/collections_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/collections_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/collections_qemu_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FixedArray push/pop order is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/collections_qemu_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FixedMap hash/put/get is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/collections_qemu_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RingBuffer enqueue/dequeue with wrap-around is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
