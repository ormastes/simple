# access_cli_grammar_spec

> Purpose: Prove that T32 shared GUI access grammar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# access_cli_grammar_spec

Purpose: Prove that T32 shared GUI access grammar.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/access_cli_grammar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that T32 shared GUI access grammar.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### T32 shared GUI access grammar

#### projects the six overlapping operations without changing the T32 catalog

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects the six overlapping operations without changing the T32 catalog
- Verify: projects the six overlapping operations without changing the T32 catalog
   - Expected: all_cli_commands().len() equals `36`
   - Expected: shared.len() equals `6`
   - Expected: shared[0].operation equals `ACCESS_OPERATION_LIST`
   - Expected: shared[1].operation equals `ACCESS_OPERATION_SNAPSHOT`
   - Expected: shared[2].operation equals `ACCESS_OPERATION_SURFACE`
   - Expected: shared[3].operation equals `ACCESS_OPERATION_FIND`
   - Expected: shared[4].operation equals `ACCESS_OPERATION_ACT`
   - Expected: shared[5].operation equals `ACCESS_OPERATION_HISTORY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("projects the six overlapping operations without changing the T32 catalog")
step("Verify: projects the six overlapping operations without changing the T32 catalog")
# @req: REQ-APP-T32-CLI-001
expect(all_cli_commands().len()).to_equal(36)  # oracle: 36 — named expected value from the requirement
val shared = shared_access_commands()
expect(shared.len()).to_equal(6)  # oracle: 6 — named expected value from the requirement
expect(shared[0].operation).to_equal(ACCESS_OPERATION_LIST)
expect(shared[1].operation).to_equal(ACCESS_OPERATION_SNAPSHOT)
expect(shared[2].operation).to_equal(ACCESS_OPERATION_SURFACE)
expect(shared[3].operation).to_equal(ACCESS_OPERATION_FIND)
expect(shared[4].operation).to_equal(ACCESS_OPERATION_ACT)
expect(shared[5].operation).to_equal(ACCESS_OPERATION_HISTORY)
```

</details>

#### keeps reads safe and marks action execution explicitly

- keeps reads safe and marks action execution explicitly
- Verify: keeps reads safe and marks action execution explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps reads safe and marks action execution explicitly")
step("Verify: keeps reads safe and marks action execution explicitly")
val reads = shared_access_commands()
expect(reads[0].safety.read_only).to_be(true)
expect(reads[1].safety.read_only).to_be(true)
expect(reads[2].safety.read_only).to_be(true)
expect(reads[3].safety.read_only).to_be(true)
expect(reads[5].safety.read_only).to_be(true)
expect(reads[4].safety.read_only).to_be(false)
expect(reads[4].safety.destructive).to_be(true)
expect(reads[4].safety.requires_confirmation).to_be(true)
expect(reads[4].safety.may_prompt).to_be(true)
```

</details>

#### requires confirmation and preserves a correlated error request id

- requires confirmation and preserves a correlated error request id
- Verify: requires confirmation and preserves a correlated error request id
   - Expected: t32_cli_main(["action", "do", "step", "--json"]) equals `1`
   - Expected: MCP_T32_HISTORY.len() equals `before + 2`
   - Expected: request.command equals `access_request action`
   - Expected: result.command equals `access_result action`
   - Expected: result.request_id equals `request.request_id`
   - Expected: result.result equals `code=interaction_required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires confirmation and preserves a correlated error request id")
step("Verify: requires confirmation and preserves a correlated error request id")
val before = MCP_T32_HISTORY.len()
expect(t32_cli_main(["action", "do", "step", "--json"])).to_equal(1)
expect(MCP_T32_HISTORY.len()).to_equal(before + 2)
val request = MCP_T32_HISTORY[MCP_T32_HISTORY.len() - 2]
val result = MCP_T32_HISTORY[MCP_T32_HISTORY.len() - 1]
expect(request.command).to_equal("access_request action")
expect(result.command).to_equal("access_result action")
expect(request.request_id).to_start_with("t32-action-")
expect(result.request_id).to_equal(request.request_id)
expect(result.result).to_equal("code=interaction_required")
```

</details>

#### generates distinct process-scoped action ids and rejects bridge bypasses

- generates distinct process-scoped action ids and rejects bridge bypasses
- Verify: generates distinct process-scoped action ids and rejects bridge bypasses


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates distinct process-scoped action ids and rejects bridge bypasses")
step("Verify: generates distinct process-scoped action ids and rejects bridge bypasses")
val first_id = t32_action_request_id()
val second_id = t32_action_request_id()
expect(first_id).to_start_with("t32-action-")
assert_not_equal(second_id, first_id)
match bridge_action_invoke("step", ""):
    Ok(_): fail("unconfirmed bridge action accepted")
    Err(message): expect(message).to_contain("confirmation")
```

</details>

#### expands catalog placeholders and rejects unresolved action arguments

- expands catalog placeholders and rejects unresolved action arguments
- Verify: expands catalog placeholders and rejects unresolved action arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("expands catalog placeholders and rejects unresolved action arguments")
step("Verify: expands catalog placeholders and rejects unresolved action arguments")
match t32_action_command("Break.Set {symbol}", "main"):
    Err(message): fail("named placeholder rejected: " + message)
    Ok(command): expect(command).to_equal("Break.Set main")
match t32_action_command("FLASH.ReProgram ALL; Data.LOAD.Elf {elf_path}; FLASH.ReProgram OFF", "app.elf"):
    Err(message): fail("catalog elf placeholder rejected: " + message)
    Ok(command): expect(command).to_contain("Data.LOAD.Elf app.elf")
match t32_action_command("Step", "unexpected"):
    Ok(_): fail("unused action argument accepted")
    Err(message): expect(message).to_contain("does not accept")
match t32_action_command("Break.Set {symbol}", ""):
    Ok(_): fail("missing named action argument accepted")
    Err(message): expect(message).to_contain("required")
```

</details>

#### bounds and shell-safes user action arguments before interpolation

- bounds and shell-safes user action arguments before interpolation
- Verify: bounds and shell-safes user action arguments before interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds and shell-safes user action arguments before interpolation")
step("Verify: bounds and shell-safes user action arguments before interpolation")
match t32_action_command("Break.Set {symbol}", "safe_symbol-1"):
    Err(message): fail("safe action argument rejected: " + message)
    Ok(command): expect(command).to_equal("Break.Set safe_symbol-1")
match t32_action_command("Break.Set {symbol}", "main;touch/tmp/injected"):
    Ok(_): fail("shell command separator accepted")
    Err(message): expect(message).to_contain("Invalid action argument")
match t32_action_command("Break.Set {symbol}", "$(touch/tmp/injected)"):
    Ok(_): fail("shell substitution accepted")
    Err(message): expect(message).to_contain("Invalid action argument")
match t32_action_command("Break.Set {symbol}", "x" * (T32_ACTION_ARG_MAX_LENGTH + 1)):
    Ok(_): fail("oversized action argument accepted")
    Err(message): expect(message).to_contain("maximum length")
match t32_action_command("Register.Set %0 %1", "R0"):
    Ok(_): fail("second placeholder bypassed the one-argument bound")
    Err(message): expect(message).to_contain("at most one")
```

</details>

#### maps canonical T32 spellings to shared handler keys

- maps canonical T32 spellings to shared handler keys
- Verify: maps canonical T32 spellings to shared handler keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps canonical T32 spellings to shared handler keys")
step("Verify: maps canonical T32 spellings to shared handler keys")
match find_shared_access_command("window", "show"):
    Some(command): expect(command.handler_key).to_equal("t32_window_capture")
    nil: fail("window show mapping missing")
match find_shared_access_command("action", "do"):
    Some(command): expect(command.handler_key).to_equal("t32_action_invoke")
    nil: fail("action do mapping missing")
expect(find_shared_access_command("cmm", "")).to_be_nil()
```

</details>

#### finds global and window-targeted actions from the authoritative catalog

- finds global and window-targeted actions from the authoritative catalog
- Verify: finds global and window-targeted actions from the authoritative catalog


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("finds global and window-targeted actions from the authoritative catalog")
step("Verify: finds global and window-targeted actions from the authoritative catalog")
expect(t32_find_action("step")).to_contain("step|Single Step|execute|Step|")
expect(t32_get_window_actions("register_view").join("\n")).to_contain("refresh_registers|Refresh Registers|execute|Register.view")
```

</details>

#### keeps legacy history fields and exposes action request correlation

- keeps legacy history fields and exposes action request correlation
- Verify: keeps legacy history fields and exposes action request correlation
   - Expected: entry.request_id equals `t32-action-test`
   - Expected: history.rows[0] equals `["Command", "Result", "Session", "Core", "Request ID"]`
   - Expected: history.rows[1][4] equals `t32-action-test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps legacy history fields and exposes action request correlation")
step("Verify: keeps legacy history fields and exposes action request correlation")
t32_add_history_with_request("action:step Step", "ok", "test-session", "test-core", "t32-action-test")
val entry = MCP_T32_HISTORY[MCP_T32_HISTORY.len() - 1]
expect(entry.request_id).to_equal("t32-action-test")
match bridge_history_tail(1):
    Err(message): fail("history unavailable: " + message)
    Ok(history):
        expect(history.rows[0]).to_equal(["Command", "Result", "Session", "Core", "Request ID"])
        expect(history.rows[1][4]).to_equal("t32-action-test")
```

</details>

#### bounds TRACE32 access history at 64 correlated events

- bounds TRACE32 access history at 64 correlated events
- Verify: bounds TRACE32 access history at 64 correlated events
   - Expected: MCP_T32_HISTORY.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds TRACE32 access history at 64 correlated events")
step("Verify: bounds TRACE32 access history at 64 correlated events")
for i in 0..70:
    t32_add_history_with_request("access_result action:test", "code=ok", "test-session", "test-core", "t32-cap-" + i.to_text())
expect(MCP_T32_HISTORY.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
```

</details>

#### bounds TRACE32 subprocess execution with the shared process facade

- bounds TRACE32 subprocess execution with the shared process facade
- Verify: bounds TRACE32 subprocess execution with the shared process facade
   - Expected: timed.1 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds TRACE32 subprocess execution with the shared process facade")
step("Verify: bounds TRACE32 subprocess execution with the shared process facade")
val timed = t32_run_remote_process("sleep", ["2"], 10)
expect(timed.1).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(timed.0).to_contain("TIMEOUT")
```

</details>

#### passes shell metacharacters as data instead of commands

- passes shell metacharacters as data instead of commands
- Verify: passes shell metacharacters as data instead of commands
   - Expected: result.1 equals `0`
   - Expected: result.0 equals `literal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes shell metacharacters as data instead of commands")
step("Verify: passes shell metacharacters as data instead of commands")
val literal = "safe;printf injected"
val result = t32_run_remote_process("printf", ["%s", literal], 5000)
expect(result.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.0).to_equal(literal)
```

</details>

#### uses the common result and render owners for human and JSON output

- uses the common result and render owners for human and JSON output
- Verify: uses the common result and render owners for human and JSON output
   - Expected: result.rows[0] equals `["ID", "TITLE", "OWNER", "KIND", "STATE", "GEOMETRY", "FOCUS", "VISIBLE", "PA... (full value in folded executable source)`
   - Expected: result.rows[1].len() equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the common result and render owners for human and JSON output")
step("Verify: uses the common result and render owners for human and JSON output")
var result = T32BridgeResult.empty("scalar")
match bridge_window_list():
    Err(message): fail("window catalog unavailable: " + message)
    Ok(listed): result = listed
expect(result.rows[0]).to_equal(["ID", "TITLE", "OWNER", "KIND", "STATE", "GEOMETRY", "FOCUS", "VISIBLE", "PARENT", "CAPS", "REVISION", "CAPTURED_AT", "GENERATION", "STALE"])
expect(result.rows[1].len()).to_equal(14)  # oracle: 14 — named expected value from the requirement
val human = render_result(result)
expect(human).to_contain("CAPTURED_AT")
expect(human).to_contain("trace32:register_view")
val json = access_render_json(result)
expect(json).to_contain("\"schema\":\"simple.access/v1\"")
expect(json).to_contain("\"operation\":\"list\"")
expect(json).to_contain("\"source\":{\"id\":\"t32\"")
expect(json).to_contain("\"items\":[{")
expect(json).to_contain("\"id\":\"trace32:register_view\"")
expect(json).to_contain("\"owner\":\"trace32\"")
expect(json).to_contain("\"surface_kind\":\"trace32_window\"")
```

</details>

#### validates shared requests and consumes JSON mode only for them

- validates shared requests and consumes JSON mode only for them
- Verify: validates shared requests and consumes JSON mode only for them


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("validates shared requests and consumes JSON mode only for them")
step("Verify: validates shared requests and consumes JSON mode only for them")
match prepare_access_args(["window", "show", "register_view", "--json"]):
    Err(error): fail("valid shared request rejected: " + error.message)
    Ok(shared): expect(shared).to_equal(["window", "show", "register_view"])
match prepare_access_args(["window", "show", "--json"]):
    Ok(_): fail("missing shared arguments accepted")
    Err(error): expect(error.code).to_equal("invalid_argument")
match prepare_access_args(["cmm", "startup.cmm", "--json"]):
    Err(error): fail("private command rejected: " + error.message)
    Ok(private): expect(private).to_equal(["cmm", "startup.cmm", "--json"])
match prepare_access_args(["window", "open", "register_view", "--json"]):
    Err(error): fail("private window open rejected: " + error.message)
    Ok(private): expect(private).to_equal(["window", "open", "register_view", "--json"])
match prepare_access_args(["action", "do", "step", "--confirm", "--json"]):
    Err(error): fail("confirmed action rejected: " + error.message)
    Ok(shared): expect(shared).to_equal(["action", "do", "step"])
```

</details>

#### returns nonzero for typed shared-command failures

- returns nonzero for typed shared-command failures
- Verify: returns nonzero for typed shared-command failures
   - Expected: t32_cli_main(["window", "show", "--json"]) equals `1`
   - Expected: t32_cli_main(["window", "show", "__missing_ui_access_window__", "--json"]) equals `1`
   - Expected: t32_cli_main(["windows", "extra"]) equals `1`
   - Expected: t32_cli_main(["window"]) equals `1`
   - Expected: t32_cli_main(["window", "unknown", "register"]) equals `1`
   - Expected: t32_cli_main(["window", "unknown", "register", "--json"]) equals `1`
   - Expected: t32_cli_main(["action", "unknown", "--json"]) equals `1`
   - Expected: t32_cli_main(["history", "many"]) equals `1`
   - Expected: t32_cli_main(["history", "0"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns nonzero for typed shared-command failures")
step("Verify: returns nonzero for typed shared-command failures")
expect(t32_cli_main(["window", "show", "--json"])).to_equal(1)
expect(t32_cli_main(["window", "show", "__missing_ui_access_window__", "--json"])).to_equal(1)
expect(t32_cli_main(["windows", "extra"])).to_equal(1)
expect(t32_cli_main(["window"])).to_equal(1)
expect(t32_cli_main(["window", "unknown", "register"])).to_equal(1)
expect(t32_cli_main(["window", "unknown", "register", "--json"])).to_equal(1)
expect(t32_cli_main(["action", "unknown", "--json"])).to_equal(1)
expect(t32_cli_main(["history", "many"])).to_equal(1)
expect(t32_cli_main(["history", "0"])).to_equal(1)
```

</details>

#### maps T-codes to stable common errors at the adapter boundary

- maps T-codes to stable common errors at the adapter boundary
- Verify: maps T-codes to stable common errors at the adapter boundary
   - Expected: missing.code equals `target_not_found`
   - Expected: missing.source_code equals `T4030`
   - Expected: invalid.code equals `invalid_argument`
   - Expected: invalid.source_code equals `T4003`
   - Expected: confirmation.code equals `interaction_required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps T-codes to stable common errors at the adapter boundary")
step("Verify: maps T-codes to stable common errors at the adapter boundary")
val missing = t32_map_access_error("T4030: Window not found: register")
expect(missing.code).to_equal("target_not_found")
expect(missing.source_code).to_equal("T4030")
val invalid = t32_map_access_error("T4003: Missing required argument")
expect(invalid.code).to_equal("invalid_argument")
expect(invalid.source_code).to_equal("T4003")
val confirmation = t32_map_access_error("explicit confirmation is required")
expect(confirmation.code).to_equal("interaction_required")
expect(confirmation.interaction_required).to_be(true)
```

</details>

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

- `REQ-SSPEC-APP`
- `REQ-APP-T32-CLI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a5d7b72fd0377c3f3e2b3ba595c3b0eb1225f8f0fb3b926095abc98e7575c62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a5d7b72fd0377c3f3e2b3ba595c3b0eb1225f8f0fb3b926095abc98e7575c62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a5d7b72fd0377c3f3e2b3ba595c3b0eb1225f8f0fb3b926095abc98e7575c62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/t32_cli/access_cli_grammar_spec.spl
mirror: doc/06_spec/01_unit/app/t32_cli/access_cli_grammar_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/t32_cli/access_cli_grammar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/t32_cli/access_cli_grammar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/t32_cli/access_cli_grammar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/t32_cli/access_cli_grammar_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects the six overlapping operations without changing the T32 catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/t32_cli/access_cli_grammar_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps reads safe and marks action execution explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/t32_cli/access_cli_grammar_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires confirmation and preserves a correlated error request id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
