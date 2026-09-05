# mcp_t32_run_guard_spec

> Purpose: Prove that T32 MCP Run Guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_t32_run_guard_spec

Purpose: Prove that T32 MCP Run Guard.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that T32 MCP Run Guard.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### T32 MCP Run Guard

#### always-allowed tools

#### allows sessions_list while running

- allows sessions_list while running
- Verify: allows sessions_list while running
   - Expected: guard_is_always_allowed("t32_sessions_list") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows sessions_list while running")
step("Verify: allows sessions_list while running")
# @req: REQ-APP-MCP-T32-001
expect(guard_is_always_allowed("t32_sessions_list")).to_equal(true)
```

</details>

#### allows session_open while running

- allows session_open while running
- Verify: allows session_open while running
   - Expected: guard_is_always_allowed("t32_session_open") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows session_open while running")
step("Verify: allows session_open while running")
expect(guard_is_always_allowed("t32_session_open")).to_equal(true)
```

</details>

#### allows window_list while running

- allows window_list while running
- Verify: allows window_list while running
   - Expected: guard_is_always_allowed("t32_window_list") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows window_list while running")
step("Verify: allows window_list while running")
expect(guard_is_always_allowed("t32_window_list")).to_equal(true)
```

</details>

#### allows history_tail while running

- allows history_tail while running
- Verify: allows history_tail while running
   - Expected: guard_is_always_allowed("t32_history_tail") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows history_tail while running")
step("Verify: allows history_tail while running")
expect(guard_is_always_allowed("t32_history_tail")).to_equal(true)
```

</details>

#### allows cmm_commands while running

- allows cmm_commands while running
- Verify: allows cmm_commands while running
   - Expected: guard_is_always_allowed("t32_cmm_commands") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows cmm_commands while running")
step("Verify: allows cmm_commands while running")
expect(guard_is_always_allowed("t32_cmm_commands")).to_equal(true)
```

</details>

#### blocked tools

#### blocks window_capture while running

- blocks window_capture while running
- Verify: blocks window_capture while running
   - Expected: guard_is_always_allowed("t32_window_capture") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks window_capture while running")
step("Verify: blocks window_capture while running")
expect(guard_is_always_allowed("t32_window_capture")).to_equal(false)
```

</details>

#### blocks screenshot while running

- blocks screenshot while running
- Verify: blocks screenshot while running
   - Expected: guard_is_always_allowed("t32_screenshot") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks screenshot while running")
step("Verify: blocks screenshot while running")
expect(guard_is_always_allowed("t32_screenshot")).to_equal(false)
```

</details>

#### blocks field_set while running

- blocks field_set while running
- Verify: blocks field_set while running
   - Expected: guard_is_always_allowed("t32_field_set") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks field_set while running")
step("Verify: blocks field_set while running")
expect(guard_is_always_allowed("t32_field_set")).to_equal(false)
```

</details>

#### safe cmd_run commands

#### allows Break command

- allows Break command
- Verify: allows Break command
   - Expected: guard_is_safe_cmd("Break") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows Break command")
step("Verify: allows Break command")
expect(guard_is_safe_cmd("Break")).to_equal(true)
```

</details>

#### allows Break.Set command

- allows Break.Set command
- Verify: allows Break.Set command
   - Expected: guard_is_safe_cmd("Break.Set main") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows Break.Set command")
step("Verify: allows Break.Set command")
expect(guard_is_safe_cmd("Break.Set main")).to_equal(true)
```

</details>

#### allows Break.Delete command

- allows Break.Delete command
- Verify: allows Break.Delete command
   - Expected: guard_is_safe_cmd("Break.Delete /ALL") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows Break.Delete command")
step("Verify: allows Break.Delete command")
expect(guard_is_safe_cmd("Break.Delete /ALL")).to_equal(true)
```

</details>

#### blocks Data.dump command

- blocks Data.dump command
- Verify: blocks Data.dump command
   - Expected: guard_is_safe_cmd("Data.dump") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks Data.dump command")
step("Verify: blocks Data.dump command")
expect(guard_is_safe_cmd("Data.dump")).to_equal(false)
```

</details>

#### safe eval expressions

#### allows STATE.RUN()

- allows STATE.RUN()
- Verify: allows STATE.RUN()
   - Expected: guard_is_safe_eval("STATE.RUN()") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows STATE.RUN()")
step("Verify: allows STATE.RUN()")
expect(guard_is_safe_eval("STATE.RUN()")).to_equal(true)
```

</details>

#### allows PRACTICE.STATE()

- allows PRACTICE.STATE()
- Verify: allows PRACTICE.STATE()
   - Expected: guard_is_safe_eval("PRACTICE.STATE()") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows PRACTICE.STATE()")
step("Verify: allows PRACTICE.STATE()")
expect(guard_is_safe_eval("PRACTICE.STATE()")).to_equal(true)
```

</details>

#### blocks Register(PC)

- blocks Register(PC)
- Verify: blocks Register(PC)
   - Expected: guard_is_safe_eval("Register(PC)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks Register(PC)")
step("Verify: blocks Register(PC)")
expect(guard_is_safe_eval("Register(PC)")).to_equal(false)
```

</details>

#### timeout configuration

#### returns cmm_run timeout

- returns cmm_run timeout
- Verify: returns cmm_run timeout
   - Expected: guard_get_timeout("t32_cmm_run") equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cmm_run timeout")
step("Verify: returns cmm_run timeout")
expect(guard_get_timeout("t32_cmm_run")).to_equal(60000)
```

</details>

#### returns eval timeout

- returns eval timeout
- Verify: returns eval timeout
   - Expected: guard_get_timeout("t32_eval") equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns eval timeout")
step("Verify: returns eval timeout")
expect(guard_get_timeout("t32_eval")).to_equal(3000)
```

</details>

#### returns default for unknown tool

- returns default for unknown tool
- Verify: returns default for unknown tool
   - Expected: guard_get_timeout("t32_unknown_tool") equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default for unknown tool")
step("Verify: returns default for unknown tool")
expect(guard_get_timeout("t32_unknown_tool")).to_equal(10000)
```

</details>

#### error message format

#### T4100 includes tool name

- T4100 includes tool name
- Verify: T4100 includes tool name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T4100 includes tool name")
step("Verify: T4100 includes tool name")
val msg = guard_err_target_running("t32_window_capture")
expect(msg).to_start_with("T4100")
expect(msg).to_contain("t32_window_capture")
expect(msg).to_contain("halted CPU")
```

</details>

#### T4101 includes timeout

- T4101 includes timeout
- Verify: T4101 includes timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T4101 includes timeout")
step("Verify: T4101 includes timeout")
val msg = guard_err_command_timeout("t32_eval", 3000)
expect(msg).to_start_with("T4101")
expect(msg).to_contain("3000")
```

</details>

#### T4100 suggests Break command

- T4100 suggests Break command
- Verify: T4100 suggests Break command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T4100 suggests Break command")
step("Verify: T4100 suggests Break command")
val msg = guard_err_target_running("t32_field_set")
expect(msg).to_contain("Break")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-MCP-T32-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d7804bc3b0197750aeb09742466fe8448aff7a4711ead508c8731931167d396`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d7804bc3b0197750aeb09742466fe8448aff7a4711ead508c8731931167d396`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d7804bc3b0197750aeb09742466fe8448aff7a4711ead508c8731931167d396`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_run_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_run_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_run_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows sessions_list while running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows session_open while running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_run_guard_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows window_list while running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
