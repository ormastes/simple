# Debug Session Specification

> <details>

<!-- sdn-diagram:id=debug_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_session_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Session Specification

## Scenarios

### MCP Debug Session Manager

#### creates and lists sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val s1 = mgr.create_session("prog1.spl", "interpreter")
val s2 = mgr.create_session("prog2.spl", "smf")
expect(s1.id).to_equal("session_1")
expect(s2.id).to_equal("session_2")
expect(mgr.list_sessions().len()).to_equal(2)
```

</details>

#### finds and removes sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val s1 = mgr.create_session("prog.spl", "interpreter")
expect(mgr.find_session(s1.id)).to_equal(0)
expect(mgr.find_session("missing")).to_equal(-1)
expect(mgr.remove_session("missing")).to_equal(false)
expect(mgr.remove_session(s1.id)).to_equal(true)
expect(mgr.list_sessions().len()).to_equal(0)
```

</details>

#### adds and removes breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val s1 = mgr.create_session("prog.spl", "interpreter")
val bp1 = mgr.add_breakpoint(s1.id, "file.spl", 10, "")
val bp2 = mgr.add_breakpoint(s1.id, "file.spl", 20, "x > 0")
expect(bp1).to_equal("1")
expect(bp2).to_equal("2")
val sessions = mgr.list_sessions()
expect(sessions[0].breakpoints.len()).to_equal(2)
expect(mgr.remove_breakpoint(s1.id, "1")).to_equal(true)
expect(mgr.remove_breakpoint(s1.id, "bad")).to_equal(false)
expect(mgr.remove_breakpoint("missing", "1")).to_equal(false)
val after = mgr.list_sessions()
expect(after[0].breakpoints.len()).to_equal(1)
```

</details>

#### handles missing sessions for add_breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val bp = mgr.add_breakpoint("missing", "file.spl", 1, "")
expect(bp).to_equal("")
```

</details>

#### updates session state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val s1 = mgr.create_session("prog.spl", "interpreter")
expect(mgr.set_state("missing", "running")).to_equal(false)
expect(mgr.set_state(s1.id, "running")).to_equal(true)
val sessions = mgr.list_sessions()
expect(sessions[0].state).to_equal("running")
```

</details>

#### adds and removes data breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val s1 = mgr.create_session("prog.spl", "interpreter")
val dbp1 = mgr.add_data_breakpoint(s1.id, "counter", "write", "")
val dbp2 = mgr.add_data_breakpoint(s1.id, "total", "readWrite", "total > 10")
expect(dbp1).to_equal("1")
expect(dbp2).to_equal("2")
val sessions = mgr.list_sessions()
expect(sessions[0].data_breakpoints.len()).to_equal(2)
expect(mgr.remove_data_breakpoint(s1.id, "1")).to_equal(true)
expect(mgr.remove_data_breakpoint(s1.id, "bad")).to_equal(false)
expect(mgr.remove_data_breakpoint("missing", "1")).to_equal(false)
val after = mgr.list_sessions()
expect(after[0].data_breakpoints.len()).to_equal(1)
```

</details>

#### handles missing sessions for data breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SessionManager.empty()
val dbp = mgr.add_data_breakpoint("missing", "x", "write", "")
expect(dbp).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/debug_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Debug Session Manager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
