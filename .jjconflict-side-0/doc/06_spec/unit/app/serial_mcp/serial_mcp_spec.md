# Serial Mcp Specification

> Tests covering SerialPort, serial_open, SshSerialSession, ssh_serial_connect, ssh_serial_connect_native, SshSerialExecResult, ssh_serial_exec, MCP Tool Dispatch, detect_tool_name, get_arg, get_arg_int, MCP Protocol, make_tool_serial_open schema, make_tool_ssh_serial_exec schema.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Mcp Specification

## Scenarios

### SerialPort

### serial_open

#### BLOCKED: AC-4: serial_open requires SIMPLE_HW_TEST=1 and SIGSEGV guard

- BLOCKED: AC-4: serial_open requires SIMPLE_HW_TEST=1 and SIGSEGV guard
   - Expected: test_env_require("SIMPLE_HW_TEST") equals `blocked:SIMPLE_HW_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLOCKED: AC-4: serial_open requires SIMPLE_HW_TEST=1 and SIGSEGV guard")
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### SshSerialSession

### ssh_serial_connect

#### BLOCKED: AC-1: ssh_serial_connect requires SIMPLE_HW_TEST=1 and SIGSEGV guard

- BLOCKED: AC-1: ssh_serial_connect requires SIMPLE_HW_TEST=1 and SIGSEGV guard
   - Expected: test_env_require("SIMPLE_HW_TEST") equals `blocked:SIMPLE_HW_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLOCKED: AC-1: ssh_serial_connect requires SIMPLE_HW_TEST=1 and SIGSEGV guard")
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### ssh_serial_connect_native

#### BLOCKED: AC-2: ssh_serial_connect_native requires SIMPLE_HW_TEST=1 and SIGSEGV guard

- BLOCKED: AC-2: ssh_serial_connect_native requires SIMPLE_HW_TEST=1 and SIGSEGV guard
   - Expected: test_env_require("SIMPLE_HW_TEST") equals `blocked:SIMPLE_HW_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLOCKED: AC-2: ssh_serial_connect_native requires SIMPLE_HW_TEST=1 and SIGSEGV guard")
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### SshSerialExecResult

### ssh_serial_exec

#### BLOCKED: AC-3: ssh_serial_exec requires SIMPLE_HW_TEST=1 and SIGSEGV guard

- BLOCKED: AC-3: ssh_serial_exec requires SIMPLE_HW_TEST=1 and SIGSEGV guard
   - Expected: test_env_require("SIMPLE_HW_TEST") equals `blocked:SIMPLE_HW_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLOCKED: AC-3: ssh_serial_exec requires SIMPLE_HW_TEST=1 and SIGSEGV guard")
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### MCP Tool Dispatch

### detect_tool_name

#### AC-5: extracts tool name from tools/call body

- AC-5: extracts tool name from tools/call body
   - Expected: detect_tool_name(body) equals `ssh_serial_exec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: extracts tool name from tools/call body")
val body = "{\"params\":{\"name\":\"ssh_serial_exec\",\"arguments\":{}}}"
expect(detect_tool_name(body)).to_equal("ssh_serial_exec")
```

</details>

#### AC-5: extracts serial_open from body

- AC-5: extracts serial_open from body
   - Expected: detect_tool_name(body) equals `serial_open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: extracts serial_open from body")
val body = "{\"params\":{\"name\":\"serial_open\",\"arguments\":{}}}"
expect(detect_tool_name(body)).to_equal("serial_open")
```

</details>

### get_arg

#### AC-5: extracts string argument from simple body

- AC-5: extracts string argument from simple body
   - Expected: result equals `val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: extracts string argument from simple body")
# Was `expect(found or not found).to_equal(true)` — a tautology that
# held for every possible return value, including the wrong ones.
val result = get_arg("{\"params\":{\"name\":\"t\",\"arguments\":{\"key\":\"val\"}}}", "key")
expect(result).to_equal("val")
```

</details>

#### AC-5: returns empty text when the argument is absent

- AC-5: returns empty text when the argument is absent
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns empty text when the argument is absent")
val result = get_arg("{\"params\":{\"name\":\"t\",\"arguments\":{}}}", "key")
expect(result).to_equal("")
```

</details>

### get_arg_int

#### AC-5: returns default when argument missing

- AC-5: returns default when argument missing
   - Expected: get_arg_int(body, "baud", 9600) equals `9600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns default when argument missing")
val body = "{\"params\":{\"name\":\"t\",\"arguments\":{}}}"
expect(get_arg_int(body, "baud", 9600)).to_equal(9600)
```

</details>

### MCP Protocol

### make_tool_serial_open schema

#### AC-5: schema contains tool name

- AC-5: schema contains tool name
   - Expected: schema contains `serial_open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: schema contains tool name")
val schema = make_tool_serial_open()
expect(schema.contains("serial_open")).to_equal(true)
```

</details>

#### AC-5: schema contains device property

- AC-5: schema contains device property
   - Expected: schema contains `device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: schema contains device property")
val schema = make_tool_serial_open()
expect(schema.contains("device")).to_equal(true)
```

</details>

#### AC-5: schema contains baud property

- AC-5: schema contains baud property
   - Expected: schema contains `baud`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: schema contains baud property")
val schema = make_tool_serial_open()
expect(schema.contains("baud")).to_equal(true)
```

</details>

### make_tool_ssh_serial_exec schema

#### AC-5: schema contains cmd property

- AC-5: schema contains cmd property
   - Expected: schema contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: schema contains cmd property")
val schema = make_tool_ssh_serial_exec()
expect(schema.contains("cmd")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/serial_mcp/serial_mcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SerialPort, serial_open, SshSerialSession, ssh_serial_connect, ssh_serial_connect_native, SshSerialExecResult, ssh_serial_exec, MCP Tool Dispatch, detect_tool_name, get_arg, get_arg_int, MCP Protocol, make_tool_serial_open schema, make_tool_ssh_serial_exec schema.
- SerialPort
- serial_open
- SshSerialSession
- ssh_serial_connect
- ssh_serial_connect_native
- SshSerialExecResult
- ssh_serial_exec
- MCP Tool Dispatch
- detect_tool_name
- get_arg
- get_arg_int
- MCP Protocol
- make_tool_serial_open schema
- make_tool_ssh_serial_exec schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `8602add622436e0f2d79a6e39dcbbfed3ac0cced4167893d76c4f2db2bcfb38d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8602add622436e0f2d79a6e39dcbbfed3ac0cced4167893d76c4f2db2bcfb38d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8602add622436e0f2d79a6e39dcbbfed3ac0cced4167893d76c4f2db2bcfb38d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/serial_mcp/serial_mcp_spec.spl
mirror: doc/06_spec/unit/app/serial_mcp/serial_mcp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/serial_mcp/serial_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/serial_mcp/serial_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/serial_mcp/serial_mcp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/serial_mcp/serial_mcp_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKED: AC-4: serial_open requires SIMPLE_HW_TEST=1 and SIGSEGV guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/serial_mcp/serial_mcp_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKED: AC-1: ssh_serial_connect requires SIMPLE_HW_TEST=1 and SIGSEGV guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/serial_mcp/serial_mcp_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKED: AC-2: ssh_serial_connect_native requires SIMPLE_HW_TEST=1 and SIGSEGV guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
