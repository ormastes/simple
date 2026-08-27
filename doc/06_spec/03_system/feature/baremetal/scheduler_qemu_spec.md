# Scheduler QEMU Tests

> Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task execution via semihost output. Tests that the bare-metal task scheduler correctly manages context switching, priority ordering, and task lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler QEMU Tests

Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task execution via semihost output. Tests that the bare-metal task scheduler correctly manages context switching, priority ordering, and task lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/scheduler_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task
execution via semihost output. Tests that the bare-metal task scheduler correctly
manages context switching, priority ordering, and task lifecycle.

## Scenarios

### Scheduler QEMU Tests

<details>
<summary>Advanced: highest priority task completes first</summary>

#### highest priority task completes first _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- highest priority task completes first


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("highest priority task completes first")
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: highest priority task completes first")
else:
    print "SKIP: Binary not built: {BINARY_PATH}"
```

</details>


</details>

<details>
<summary>Advanced: all tasks complete after sufficient ticks</summary>

#### all tasks complete after sufficient ticks _(slow)_

- all tasks complete after sufficient ticks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all tasks complete after sufficient ticks")
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: all tasks complete after sufficient ticks")
else:
    print "SKIP: Binary not built"
```

</details>


</details>

<details>
<summary>Advanced: tick count matches total work</summary>

#### tick count matches total work _(slow)_

- tick count matches total work


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tick count matches total work")
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: tick count matches total work (6 ticks)")
else:
    print "SKIP: Binary not built"
```

</details>


</details>

<details>
<summary>Advanced: all scheduler tests complete</summary>

#### all scheduler tests complete _(slow)_

- all scheduler tests complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all scheduler tests complete")
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("=== Scheduler Tests Complete ===")
else:
    print "SKIP: Binary not built"
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

- Canonical SPipe generation for source `abbdb189177c45ed56505d74a0169e68152a240e51a57782b5ce1c26ded1a813`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abbdb189177c45ed56505d74a0169e68152a240e51a57782b5ce1c26ded1a813`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abbdb189177c45ed56505d74a0169e68152a240e51a57782b5ce1c26ded1a813`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/baremetal/scheduler_qemu_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/scheduler_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/scheduler_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/scheduler_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/scheduler_qemu_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'highest priority task completes first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/scheduler_qemu_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all tasks complete after sufficient ticks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/scheduler_qemu_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tick count matches total work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
