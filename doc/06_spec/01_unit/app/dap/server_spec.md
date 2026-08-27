# Server Specification

> Tests covering DebuggerState, DapServer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Specification

## Scenarios

### DebuggerState

#### has correct state values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct state values


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct state values")
# The stub described "stopped, running, disconnected" -- the real
# enum (src/lib/nogc_sync_mut/dap/dap_types.spl) has six variants and
# uses "Terminated", not "disconnected".
val dap_types = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_types.spl")
expect(dap_types).to_contain("enum DebuggerState:")
expect(dap_types).to_contain("Uninitialized")
expect(dap_types).to_contain("Initialized")
expect(dap_types).to_contain("Launched")
expect(dap_types).to_contain("Running")
expect(dap_types).to_contain("Stopped")
expect(dap_types).to_contain("Terminated")
```

</details>

#### transitions correctly

- transitions correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions correctly")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("self.state = DebuggerState.Initialized")
expect(server).to_contain("self.state = DebuggerState.Launched")
expect(server).to_contain("self.state = DebuggerState.Running")
expect(server).to_contain("self.state = DebuggerState.Stopped")
expect(server).to_contain("self.state = DebuggerState.Terminated")
```

</details>

### DapServer

#### initializes with capabilities

- initializes with capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with capabilities")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("val capabilities = protocol.Capabilities.default()")
expect(server).to_contain("transport.write_response(request_seq, true, command, Some(capabilities))?")
```

</details>

#### handles launch request

- handles launch request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles launch request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("fn handle_launch(request_seq: Int, command: String, arguments: Option<Dict>) -> Result<Nil, String>:")
expect(server).to_contain("self.adapter.attach(self.launch_config.program, self.launch_config.args)?")
```

</details>

#### handles attach request

- handles attach request


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles attach request")
# KNOWN GAP: handle_request()'s command match has no "attach" case at
# all -- only "launch". A DAP "attach" request currently falls
# through to the unknown-command branch. Asserting the described
# behaviour honestly so this fails until an attach handler exists.
# See doc/08_tracking/bug/dap_spec_stubs_reported_green_without_asserting_2026-08-08.md
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"attach\":")
```

</details>

#### handles disconnect request

- handles disconnect request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles disconnect request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"disconnect\":")
expect(server).to_contain("self.state = DebuggerState.Terminated")
```

</details>

#### handles set breakpoints request

- handles set breakpoints request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles set breakpoints request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(server).to_contain("case \"setBreakpoints\":")
expect(handlers).to_contain("val bp_result = self.adapter.set_breakpoint_rich(")
```

</details>

#### handles continue request

- handles continue request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles continue request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"continue\":")
expect(server).to_contain("self.adapter.resume()?")
```

</details>

#### handles step over request

- handles step over request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles step over request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"next\":")
expect(server).to_contain("self.adapter.step_over()?")
```

</details>

#### handles step in request

- handles step in request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles step in request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"stepIn\":")
expect(server).to_contain("self.adapter.single_step()?")
```

</details>

#### handles step out request

- handles step out request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles step out request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"stepOut\":")
expect(server).to_contain("self.adapter.step_out()?")
```

</details>

#### handles stack trace request

- handles stack trace request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles stack trace request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"stackTrace\":")
expect(server).to_contain("val adapter_frames = self.adapter.stack_trace()")
```

</details>

#### handles scopes request

- handles scopes request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles scopes request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("case \"scopes\":")
expect(server).to_contain("if self.adapter.capabilities().supports_registers:")
```

</details>

#### handles variables request

- handles variables request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles variables request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(server).to_contain("case \"variables\":")
expect(handlers).to_contain("fn handle_variables(request_seq: Int, command: String, arguments: Option<Dict>) -> Result<Nil, String>:")
```

</details>

#### handles evaluate request

- handles evaluate request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles evaluate request")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(server).to_contain("case \"evaluate\":")
expect(handlers).to_contain("val eval_result = self.adapter.evaluate(expression)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DebuggerState, DapServer.
- DebuggerState
- DapServer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `fa7222b1ca3089d56d26538e94c021b6b24315f6868483594117e8eab74872ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa7222b1ca3089d56d26538e94c021b6b24315f6868483594117e8eab74872ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa7222b1ca3089d56d26538e94c021b6b24315f6868483594117e8eab74872ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/server_spec.spl
mirror: doc/06_spec/01_unit/app/dap/server_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/server_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct state values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/server_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transitions correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/server_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
