# Tmux API Library Specification

> Tests for the `std.tmux` module which provides a read/write interface to the tmux terminal multiplexer. The module wraps tmux CLI commands via `shell()` to list sessions, windows, panes, capture pane content, and send keystrokes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux API Library Specification

Tests for the `std.tmux` module which provides a read/write interface to the tmux terminal multiplexer. The module wraps tmux CLI commands via `shell()` to list sessions, windows, panes, capture pane content, and send keystrokes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TMUX-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/std/tmux/tmux_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the `std.tmux` module which provides a read/write interface
to the tmux terminal multiplexer. The module wraps tmux CLI commands
via `shell()` to list sessions, windows, panes, capture pane content,
and send keystrokes.

## Key Concepts

| Concept | Description |
|---------|-------------|
| TmuxSession | A named tmux session with windows count and attached state |
| TmuxWindow | A window within a session, identified by index |
| TmuxPane | A pane within a window, with dimensions and running command |
| TmuxCaptureResult | Content captured from a pane with row count |
| capture-pane | Reads visible content from a tmux pane |
| send-keys | Sends keystroke sequences to a tmux pane |

## Behavior

- All functions gracefully handle missing tmux or inactive server
- Listing functions return empty arrays when target doesn't exist
- Mutation functions return Result<T, text> for error handling
- Capture returns empty content for non-existent panes
- Struct types are plain data containers with no invariants

## Examples

```simple
use std.spec.step

use std.tmux.*

# Check if tmux is available
if tmux_available():
    val sessions = tmux_list_sessions()
    for s in sessions:
        print "Session: {s.name} ({s.windows} windows)"

    # Capture pane content
    val capture = tmux_capture_pane("main", 0, 0)
    print capture.content
```

## Scenarios

### Tmux Availability

#### reports whether tmux is installed

- reports whether tmux is installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports whether tmux is installed")
val available = tmux_available()
expect (available == true or available == false) to_equal true
```

</details>

#### reports server running status

- reports server running status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports server running status")
val running = tmux_server_running()
expect (running == true or running == false) to_equal true
```

</details>

### Tmux Session Operations

#### listing sessions

#### returns a list without crashing

- returns a list without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a list without crashing")
val sessions = tmux_list_sessions()
expect sessions.len() >= 0 to_equal true
```

</details>

#### checking session existence

#### returns false for non-existent session

- returns false for non-existent session


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for non-existent session")
val exists = tmux_has_session("__nonexistent_test_session_xyz__")
expect exists to_equal false
```

</details>

### Tmux Window and Pane Listing

#### listing windows

#### returns empty list for non-existent session

- returns empty list for non-existent session


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty list for non-existent session")
val windows = tmux_list_windows("__nonexistent_test_session_xyz__")
expect windows.len() to_equal 0
```

</details>

#### listing panes

#### returns empty list for non-existent target

- returns empty list for non-existent target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty list for non-existent target")
val panes = tmux_list_panes("__nonexistent_test_session_xyz__", 0)
expect panes.len() to_equal 0
```

</details>

### Tmux Pane Capture

#### returns empty capture for non-existent target

- returns empty capture for non-existent target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty capture for non-existent target")
val result = tmux_capture_pane("__nonexistent_test_session_xyz__", 0, 0)
expect result.content to_equal ""
expect result.pane_id to_contain "__nonexistent_test_session_xyz__"
```

</details>

#### formats pane_id as session:window.pane

- formats pane_id as session:window.pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats pane_id as session:window.pane")
val result = tmux_capture_pane("mysess", 2, 3)
expect result.pane_id to_equal "mysess:2.3"
```

</details>

### Tmux Data Types

#### TmuxSession

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs with all fields")
val s = TmuxSession(
    name: "dev",
    windows: 3,
    attached: true,
    created: "1234567890"
)
expect s.name to_equal "dev"
expect s.windows to_equal 3
expect s.attached to_equal true
expect s.created to_equal "1234567890"
```

</details>

#### TmuxWindow

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs with all fields")
val w = TmuxWindow(
    session: "main",
    index: 0,
    name: "editor",
    active: true,
    panes: 2
)
expect w.session to_equal "main"
expect w.index to_equal 0
expect w.name to_equal "editor"
expect w.active to_equal true
expect w.panes to_equal 2
```

</details>

#### TmuxPane

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs with all fields")
val p = TmuxPane(
    session: "main",
    window_index: 0,
    pane_index: 1,
    active: false,
    width: 120,
    height: 40,
    current_command: "bash",
    pid: 12345
)
expect p.session to_equal "main"
expect p.pane_index to_equal 1
expect p.width to_equal 120
expect p.height to_equal 40
expect p.current_command to_equal "bash"
expect p.pid to_equal 12345
```

</details>

#### TmuxCaptureResult

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs with all fields")
val r = TmuxCaptureResult(
    content: "hello world\nprompt $",
    pane_id: "main:0.0",
    rows: 24
)
expect r.content to_contain "hello world"
expect r.pane_id to_equal "main:0.0"
expect r.rows to_equal 24
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55160659876ee8fb4e2bfaca0dbb74257be433e159f76c7405c9bac024b923d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55160659876ee8fb4e2bfaca0dbb74257be433e159f76c7405c9bac024b923d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55160659876ee8fb4e2bfaca0dbb74257be433e159f76c7405c9bac024b923d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/std/tmux/tmux_api_spec.spl
mirror: doc/06_spec/01_unit/lib/std/tmux/tmux_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/tmux/tmux_api_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/01_unit/lib/std/tmux/tmux_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/tmux/tmux_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/tmux/tmux_api_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports whether tmux is installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/tmux/tmux_api_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports server running status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/tmux/tmux_api_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a list without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
