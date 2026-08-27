# Jupyter Execution System Specification

> Tests covering Jupyter Kernel Execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Execution System Specification

## Scenarios

### Jupyter Kernel Execution

<details>
<summary>Advanced: should respond to kernel_info_request</summary>

#### should respond to kernel_info_request _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should respond to kernel_info_request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should respond to kernel_info_request")
val msg = "{\"channel\":\"shell\",\"msg_type\":\"kernel_info_request\",\"msg_id\":\"test1\",\"session\":\"s1\",\"content\":{}}"
val output = send_kernel_message(msg)
expect(output).to_contain("kernel_info_reply")
expect(output).to_contain("simple")
```

</details>


</details>

<details>
<summary>Advanced: should respond to shutdown_request</summary>

#### should respond to shutdown_request _(slow)_

- should respond to shutdown_request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should respond to shutdown_request")
val msg = "{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"test2\",\"session\":\"s1\",\"content\":{}}"
val output = send_kernel_message(msg)
expect(output).to_contain("shutdown_reply")
```

</details>


</details>

<details>
<summary>Advanced: should handle is_complete_request for complete code</summary>

#### should handle is_complete_request for complete code _(slow)_

- should handle is_complete_request for complete code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle is_complete_request for complete code")
val msg = "{\"channel\":\"shell\",\"msg_type\":\"is_complete_request\",\"msg_id\":\"test3\",\"session\":\"s1\",\"content\":{\"code\":\"val x = 42\"}}"
val output = send_kernel_message(msg)
expect(output).to_contain("complete")
```

</details>


</details>

<details>
<summary>Advanced: should handle is_complete_request for incomplete code</summary>

#### should handle is_complete_request for incomplete code _(slow)_

- should handle is_complete_request for incomplete code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle is_complete_request for incomplete code")
val msg = "{\"channel\":\"shell\",\"msg_type\":\"is_complete_request\",\"msg_id\":\"test4\",\"session\":\"s1\",\"content\":{\"code\":\"fn foo():\"}}"
val output = send_kernel_message(msg)
expect(output).to_contain("incomplete")
```

</details>


</details>

<details>
<summary>Advanced: should respond to interrupt_request on the control channel (design SS5.1)</summary>

#### should respond to interrupt_request on the control channel (design SS5.1) _(slow)_

- should respond to interrupt_request on the control channel (design SS5.1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should respond to interrupt_request on the control channel (design SS5.1)")
val msg = "{\"channel\":\"control\",\"msg_type\":\"interrupt_request\",\"msg_id\":\"test5\",\"session\":\"s1\",\"content\":{}}"
val output = send_kernel_message(msg)
expect(output).to_contain("interrupt_reply")
expect(output).to_contain("\"status\":\"ok\"")
```

</details>


</details>

<details>
<summary>Advanced: should reply on the simple_lane comm with the current mode (design SS5.1, SS6)</summary>

#### should reply on the simple_lane comm with the current mode (design SS5.1, SS6) _(slow)_

- should reply on the simple_lane comm with the current mode (design SS5.1, SS6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reply on the simple_lane comm with the current mode (design SS5.1, SS6)")
val msg = "{\"channel\":\"shell\",\"msg_type\":\"comm_open\",\"msg_id\":\"test6\",\"session\":\"s1\",\"content\":{\"comm_id\":\"c1\",\"target_name\":\"simple_lane\",\"data\":{}}}"
val output = send_kernel_message(msg)
expect(output).to_contain("comm_msg")
expect(output).to_contain("\"comm_id\":\"c1\"")
expect(output).to_contain("interpreter")
```

</details>


</details>

<details>
<summary>Advanced: should change the session default mode via a simple_lane set_mode comm_msg</summary>

#### should change the session default mode via a simple_lane set_mode comm_msg _(slow)_

- should change the session default mode via a simple_lane set_mode comm_msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should change the session default mode via a simple_lane set_mode comm_msg")
val open_msg = "{\"channel\":\"shell\",\"msg_type\":\"comm_open\",\"msg_id\":\"test7a\",\"session\":\"s1\",\"content\":{\"comm_id\":\"c2\",\"target_name\":\"simple_lane\",\"data\":{}}}"
val set_msg = "{\"channel\":\"shell\",\"msg_type\":\"comm_msg\",\"msg_id\":\"test7b\",\"session\":\"s1\",\"content\":{\"comm_id\":\"c2\",\"data\":{\"set_mode\":\"interpreter\"}}}"
val combined = open_msg + "\n" + set_msg
val tmp = "/tmp/jupyter_test_multi_{rt_getpid()}_{rt_time_now_unix_micros()}.txt"
rt_file_write_text(tmp, combined + "\n")
val cmd = "RUNTIME=src/compiler_rust/target/release/simple; if [ ! -x \"$RUNTIME\" ]; then RUNTIME=src/compiler_rust/target/bootstrap/simple; fi; if [ ! -x \"$RUNTIME\" ]; then RUNTIME=bin/simple; fi; cat {tmp} | timeout 5 \"$RUNTIME\" run src/app/jupyter_kernel/main.spl 2>/dev/null"
val (output, stderr, code) = rt_process_run("bash", ["-c", cmd])
rt_file_delete(tmp)
expect(output).to_contain("\"comm_id\":\"c2\"")
expect(output).to_contain("\"mode\":\"interpreter\"")
```

</details>


</details>

<details>
<summary>Advanced: wires %reset into execute_request (P1 magics -> K1 session manager)</summary>

#### wires %reset into execute_request (P1 magics -> K1 session manager) _(slow)_

- wires %reset into execute_request (P1 magics -> K1 session manager)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wires %reset into execute_request (P1 magics -> K1 session manager)")
# Regression for a real gap P3 found: main.spl never imported
# std.notebook.magics and always passed an empty cell-override to
# execute_cell, so K3's magics were dead code -- every %-line was
# sent straight to the interpreter as source and failed to compile.
val msg = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"test8\",\"session\":\"s1\",\"content\":{\"code\":\"%reset\"}}"
val output = send_kernel_message(msg)
expect(output).to_contain("\"status\":\"ok\"")
expect(output).to_contain("session reset")
expect(output).to_not_contain("ExecutionError")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_execution_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Jupyter Kernel Execution.
- Jupyter Kernel Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
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

- Canonical SPipe generation for source `fed632c5abdf0060c9025f7fcd33eabca65b720f331090eec562ad69f07c4de0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fed632c5abdf0060c9025f7fcd33eabca65b720f331090eec562ad69f07c4de0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fed632c5abdf0060c9025f7fcd33eabca65b720f331090eec562ad69f07c4de0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/jupyter/jupyter_execution_system_spec.spl
mirror: doc/06_spec/03_system/tools/jupyter/jupyter_execution_system_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/jupyter/jupyter_execution_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/jupyter/jupyter_execution_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respond to kernel_info_request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should respond to kernel_info_request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respond to shutdown_request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should respond to shutdown_request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle is_complete_request for complete code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle is_complete_request for complete code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle is_complete_request for incomplete code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respond to interrupt_request on the control channel (design SS5.1)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_execution_system_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reply on the simple_lane comm with the current mode (design SS5.1, SS6)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
