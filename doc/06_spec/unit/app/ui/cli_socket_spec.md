# Cli Socket Specification

> Tests covering process_command get_state, process_command get_changes, process_command ping, process_command errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Socket Specification

## Scenarios

### process_command get_state

#### returns mode and focused fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns mode and focused fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns mode and focused fields")
val root = text_widget("sock_gs_root", "Hello")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "NORMAL"
expect response to_contain "mode"
```

</details>

#### reflects command mode after dispatch

- reflects command mode after dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reflects command mode after dispatch")
val root = text_widget("sock_gs_cmd_root", "Cmd")
val tree = UITree.new(root)
var session = new_session(tree)
session.dispatch(UIEvent.CommandMode)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "COMMAND"
```

</details>

### process_command get_changes

#### returns empty changes for fresh session

- returns empty changes for fresh session


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty changes for fresh session")
val root = text_widget("sock_gc_root", "Fresh")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_changes\"}")
expect response to_contain "changes"
```

</details>

#### returns changes after tree update

- returns changes after tree update


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns changes after tree update")
val root1 = column("sock_gc_upd", [
    text_widget("sock_gc_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("sock_gc_upd", [
    text_widget("sock_gc_t1", "Old"),
    text_widget("sock_gc_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 5}")
expect response to_contain "changes"
```

</details>

#### respects count parameter

- respects count parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects count parameter")
val root = text_widget("sock_gc_cnt_root", "Count")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 3}")
expect response to_contain "changes"
```

</details>

### process_command ping

#### responds with pong

- responds with pong


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds with pong")
val root = text_widget("sock_ping_root", "Ping")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"ping\"}")
expect response to_contain "pong"
```

</details>

### process_command errors

#### returns error for empty command

- returns error for empty command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for empty command")
val root = text_widget("sock_err_empty_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "")
expect response to_contain "error"
```

</details>

#### returns error for unknown command

- returns error for unknown command


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown command")
val root = text_widget("sock_err_unk_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"invalid_cmd\"}")
expect response to_contain "error"
expect response to_contain "unknown command"
```

</details>

#### returns error for empty JSON object

- returns error for empty JSON object


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for empty JSON object")
val root = text_widget("sock_err_obj_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{}")
expect response to_contain "error"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/cli_socket_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering process_command get_state, process_command get_changes, process_command ping, process_command errors.
- process_command get_state
- process_command get_changes
- process_command ping
- process_command errors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `af65373e84a0f108fa9cc13ed4a7eb113ac5d44847b6997847389328fa677138`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af65373e84a0f108fa9cc13ed4a7eb113ac5d44847b6997847389328fa677138`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af65373e84a0f108fa9cc13ed4a7eb113ac5d44847b6997847389328fa677138`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/cli_socket_spec.spl
mirror: doc/06_spec/unit/app/ui/cli_socket_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/cli_socket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/cli_socket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/cli_socket_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns mode and focused fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/cli_socket_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects command mode after dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/cli_socket_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty changes for fresh session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
