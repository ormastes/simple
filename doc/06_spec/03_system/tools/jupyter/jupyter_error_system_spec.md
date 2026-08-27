# Jupyter Error System Specification

> Tests covering Jupyter Kernel Error Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Error System Specification

## Scenarios

### Jupyter Kernel Error Handling

<details>
<summary>Advanced: should report errors for bad code</summary>

#### should report errors for bad code _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should report errors for bad code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report errors for bad code")
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"err1\",\"session\":\"s1\",\"content\":{\"code\":\"val = \"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s2\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
# Should get error reply, not crash
expect(output).to_contain("execute_reply")
```

</details>


</details>

<details>
<summary>Advanced: should survive error and handle next request</summary>

#### should survive error and handle next request _(slow)_

- should survive error and handle next request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should survive error and handle next request")
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"err2\",\"session\":\"s1\",\"content\":{\"code\":\"bad code\"}}\n{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"ok1\",\"session\":\"s1\",\"content\":{\"code\":\"print 42\"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s3\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("execute_reply")
```

</details>


</details>

<details>
<summary>Advanced: should handle comm_info_request</summary>

#### should handle comm_info_request _(slow)_

- should handle comm_info_request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle comm_info_request")
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"comm_info_request\",\"msg_id\":\"ci1\",\"session\":\"s1\",\"content\":{}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s4\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("comm_info_reply")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_error_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Jupyter Kernel Error Handling.
- Jupyter Kernel Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
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

- Canonical SPipe generation for source `385c2aa89957940ea160b9495038dfffe1457a20765533f5778ffaa9d0984e55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `385c2aa89957940ea160b9495038dfffe1457a20765533f5778ffaa9d0984e55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `385c2aa89957940ea160b9495038dfffe1457a20765533f5778ffaa9d0984e55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/jupyter/jupyter_error_system_spec.spl
mirror: doc/06_spec/03_system/tools/jupyter/jupyter_error_system_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/jupyter/jupyter_error_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/jupyter/jupyter_error_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report errors for bad code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report errors for bad code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should survive error and handle next request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should survive error and handle next request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle comm_info_request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_error_system_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle comm_info_request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
