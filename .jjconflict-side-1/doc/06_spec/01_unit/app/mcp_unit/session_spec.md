# Session Specification

> <details>

<!-- sdn-diagram:id=session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Specification

## Scenarios

### Session

#### defines debug session identity target state and launch metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mcp_session_source()

expect(src).to_contain("enum SessionState:")
expect(src).to_contain("Created")
expect(src).to_contain("Running")
expect(src).to_contain("Paused")
expect(src).to_contain("Terminated")
expect(src).to_contain("enum TargetType:")
expect(src).to_contain("Interpreter")
expect(src).to_contain("Native")
expect(src).to_contain("Remote")
expect(src).to_contain("class DebugSession:")
expect(src).to_contain("program_path: String")
expect(src).to_contain("state: SessionState")
```

</details>

#### defines session manager creation listing lookup and removal contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mcp_session_source()

expect(src).to_contain("class SessionManager:")
expect(src).to_contain("sessions: Dict<String, DebugSession>")
expect(src).to_contain("next_session_id: Int")
expect(src).to_contain("static fn empty() -> SessionManager:")
expect(src).to_contain("me create_session(target_type: TargetType, program_path: String) -> String:")
expect(src).to_contain("self.next_session_id = self.next_session_id + 1")
expect(src).to_contain("self.sessions[id] = session")
expect(src).to_contain("fn get_session(id: String) -> Option<DebugSession>:")
expect(src).to_contain("fn list_sessions() -> [DebugSession]:")
expect(src).to_contain("for (_, session) in self.sessions.items():")
expect(src).to_contain("me remove_session(id: String) -> Bool:")
expect(src).to_contain("self.sessions.remove(id)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
