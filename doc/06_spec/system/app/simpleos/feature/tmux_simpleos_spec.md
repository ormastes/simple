# Tmux Simpleos Specification

> Tests covering tmux_simpleos feature spec, REQ-001 session model, REQ-002 pane-backed shells, REQ-003 attach and detach, REQ-004 split and layout, REQ-005 input and output routing, REQ-006 state query API, REQ-007 capture api, REQ-008 compatibility facing api shape, REQ-009 native first backend, REQ-010 backend swap readiness, REQ-011 explicit non fatal failure handling, REQ-012 initial scope boundary, NFR-007 observability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux Simpleos Specification

## Scenarios

### tmux_simpleos feature spec

### REQ-001 session model

#### create a persistent session with an initial window and pane

- create a persistent session with an initial window and pane
   - Expected: session.name equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-002
# @req REQ-003
# @req REQ-004
# @req REQ-005
# @req REQ-006
# @req REQ-007
# @req REQ-008
# @req REQ-009
# @req REQ-010
# @req REQ-011
# @req REQ-012
# @req REQ-SSPEC-SYSTEM
step("create a persistent session with an initial window and pane")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("dev")
expect(session.name).to_equal("dev")

val windows = smux_list_windows(session.id)
expect(windows.len()).to_be_greater_than(0)

val panes = smux_list_panes(session.id, windows[0].id)
expect(panes.len()).to_be_greater_than(0)
```

</details>

### REQ-002 pane-backed shells

#### start panes on the native backend

- start panes on the native backend
   - Expected: panes[0].backend_kind equals `MuxBackendKind.NativeShell`
   - Expected: panes[0].state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("start panes on the native backend")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("shells")
val windows = smux_list_windows(session.id)
val panes = smux_list_panes(session.id, windows[0].id)

expect(panes[0].backend_kind).to_equal(MuxBackendKind.NativeShell)
expect(panes[0].state).to_equal("running")
```

</details>

### REQ-003 attach and detach

#### detach a client without destroying the session

- detach a client without destroying the session
   - Expected: smux_attach(session.id, "client-a", 120, 40).attached is true
   - Expected: smux_detach("client-a") is true
   - Expected: sessions[0].name equals `attach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detach a client without destroying the session")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("attach")
expect(smux_attach(session.id, "client-a", 120, 40).attached).to_equal(true)
expect(smux_detach("client-a")).to_equal(true)

val sessions = smux_list_sessions()
expect(sessions[0].name).to_equal("attach")
```

</details>

### REQ-004 split and layout

#### split the active pane and create a second pane

- split the active pane and create a second pane
   - Expected: smux_split_pane(session.id, window.id, first.id, "horizontal").is_ok() is true
   - Expected: panes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("split the active pane and create a second pane")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("split")
val window = smux_list_windows(session.id)[0]
val first = smux_list_panes(session.id, window.id)[0]

expect(smux_split_pane(session.id, window.id, first.id, "horizontal").is_ok()).to_equal(true)

val panes = smux_list_panes(session.id, window.id)
expect(panes.len()).to_equal(2)  # oracle: panes.len() must equal 2 — authoritative contract constant
```

</details>

### REQ-005 input and output routing

The positive fixture spawns a real shell child, sends distinct text and command nonces, and requires both child-generated GOT prefixes. It polls at most 60 times with 50 ms sleeps and closes the owned pane before final output assertions. A separate empty-pane scenario requires typed no-child errors; no fabricated send counters are used.

Validation status: source contract updated during branch synchronization; runtime execution of these revised scenarios is **UNRUN**. The positive fixture requires the same `/bin/sh` provider as `smux_terminal_service_spec.spl` (Git Bash on Windows).

<details>
<summary>Executable SSpec</summary>

Source: `test/system/app/simpleos/feature/tmux_simpleos_spec.spl`. Run the owning spec with its existing imports.

```simple
fn _await_routed_output(sid: text, wid: text, pid: text) -> text:
    var attempts = 0
    var seen = ""
    while attempts < 60 and not (seen.contains("GOT:text7f3a") and seen.contains("GOT:command9b2c")):
        thread_sleep_ms(50)
        val captured = smux_capture(sid, wid, pid, 20)
        if captured.is_ok():
            seen = captured.unwrap().content
        attempts = attempts + 1
    return seen

describe "REQ-005 input and output routing":
    it "route sent text and commands to the selected pane":
        # @req REQ-005
        step("route sent text and commands to the selected pane")
        smux_reset_for_test()
        val session = smux_create_session("routed-io")
        val window = smux_list_windows(session.id)[0]
        val pane = smux_list_panes(session.id, window.id)[0]
        expect(smux_focus_pane(session.id, window.id, pane.id)).to_equal(true)
        val spawned = smux_pane_spawn(session.id, window.id, pane.id, "/bin/sh",
            ["-c", "while read l; do echo \"GOT:$l\"; done"])
        expect(spawned.is_ok()).to_equal(true)

        val sent_text = smux_send_text(session.id, window.id, pane.id, "text7f3a\n")
        val sent_command = smux_send_command(session.id, window.id, pane.id, "command9b2c")
        val seen = _await_routed_output(session.id, window.id, pane.id)
        val closed = smux_close_pane(session.id, window.id, pane.id)
        expect(sent_text.is_ok()).to_equal(true)
        expect(sent_command.is_ok()).to_equal(true)
        expect(closed).to_equal(true)
        expect(seen).to_equal("GOT:text7f3a\nGOT:command9b2c")

    it "reject input for a selected pane without a child":
        # @req REQ-SSPEC-SYSTEM
        step("reject input for a selected pane without a child")
        # evidence(protocol_json): asserted result fields below are the complete typed oracle
        smux_reset_for_test()
        val session = smux_create_session("io")
        val window = smux_list_windows(session.id)[0]
        val pane = smux_list_panes(session.id, window.id)[0]

        expect(smux_focus_pane(session.id, window.id, pane.id)).to_equal(true)
        val text_result = smux_send_text(session.id, window.id, pane.id, "echo hi")
        expect(text_result.is_err()).to_equal(true)
        expect(text_result.err().unwrap()).to_equal("pane has no child: " + pane.id)
        val command_result = smux_send_command(session.id, window.id, pane.id, "pwd")
        expect(command_result.is_err()).to_equal(true)
        expect(command_result.err().unwrap()).to_equal("pane has no child: " + pane.id)
```

</details>

### REQ-006 state query API

#### list sessions windows and panes with stable metadata

- list sessions windows and panes with stable metadata
   - Expected: sessions[0].name equals `query`
   - Expected: windows[0].session_id equals `session.id`
   - Expected: panes[0].window_id equals `windows[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("list sessions windows and panes with stable metadata")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("query")
val sessions = smux_list_sessions()
expect(sessions[0].name).to_equal("query")

val windows = smux_list_windows(session.id)
expect(windows[0].session_id).to_equal(session.id)

val panes = smux_list_panes(session.id, windows[0].id)
expect(panes[0].window_id).to_equal(windows[0].id)
```

</details>

### REQ-007 capture api

Capture must return Ok for an existing empty pane, preserve its identity, and report empty content and zero rows. An unknown pane must return the exact typed error.

Validation status: source contract updated during branch synchronization; runtime execution of these revised scenarios is **UNRUN**. The positive fixture requires the same `/bin/sh` provider as `smux_terminal_service_spec.spl` (Git Bash on Windows).

<details>
<summary>Executable SSpec</summary>

Source: `test/system/app/simpleos/feature/tmux_simpleos_spec.spl`. Run the owning spec with its existing imports.

```simple
describe "REQ-007 capture api":
    it "capture pane output and preserve pane identity":
        # @req REQ-SSPEC-SYSTEM
        step("capture pane output and preserve pane identity")
        # evidence(protocol_json): asserted result fields below are the complete typed oracle
        smux_reset_for_test()
        val session = smux_create_session("capture")
        val window = smux_list_windows(session.id)[0]
        val pane = smux_list_panes(session.id, window.id)[0]

        val result = smux_capture(session.id, window.id, pane.id, 50)
        expect(result.is_ok()).to_equal(true)
        val capture = result.unwrap()
        expect(capture.pane_id).to_equal(pane.id)
        expect(capture.content).to_equal("")
        expect(capture.rows).to_equal(0)

        val missing = smux_capture(session.id, window.id, "missing-pane", 50)
        expect(missing.is_err()).to_equal(true)
        expect(missing.err().unwrap()).to_equal("unknown pane: missing-pane")
```

</details>

### REQ-008 compatibility facing api shape

#### expose tmux-shaped session window pane operations over the native backend

- expose tmux-shaped session window pane operations over the native backend
   - Expected: window.name equals `build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expose tmux-shaped session window pane operations over the native backend")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("compat")
val window = smux_new_window(session.id, "build")
expect(window.name).to_equal("build")

val panes = smux_list_panes(session.id, window.id)
expect(panes.len()).to_be_greater_than(0)
```

</details>

### REQ-009 native first backend

#### identify the backend as native rather than host tmux

- identify the backend as native rather than host tmux
   - Expected: smux_backend_contract_name() equals `smux-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identify the backend as native rather than host tmux")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
expect(smux_backend_contract_name()).to_equal("smux-native")
```

</details>

### REQ-010 backend swap readiness

#### keep backend identity behind a named contract boundary

- keep backend identity behind a named contract boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keep backend identity behind a named contract boundary")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
expect(smux_backend_contract_name()).to_start_with("smux-")
```

</details>

### REQ-011 explicit non fatal failure handling

#### return an error for an invalid pane target

- return an error for an invalid pane target
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("return an error for an invalid pane target")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("errors")
val window = smux_list_windows(session.id)[0]

val result = smux_resize(session.id, window.id, "missing-pane", 80, 24)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("pane")
```

</details>

#### return an error when split target is invalid

- return an error when split target is invalid
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("return an error when split target is invalid")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
val session = smux_create_session("split-errors")
val window = smux_list_windows(session.id)[0]
val result = smux_split_pane(session.id, window.id, "missing-pane", "vertical")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-012 initial scope boundary

#### expose deferred parity features explicitly

- expose deferred parity features explicitly
   - Expected: smux_is_deferred_feature("copy-mode") is true
   - Expected: smux_is_deferred_feature("mouse") is true
   - Expected: smux_is_deferred_feature("key-table-compat") is true
   - Expected: smux_is_deferred_feature("tmux-conf") is true
   - Expected: smux_is_deferred_feature("control-mode") is true
   - Expected: smux_is_deferred_feature("split-pane") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expose deferred parity features explicitly")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
smux_reset_for_test()
expect(smux_is_deferred_feature("copy-mode")).to_equal(true)
expect(smux_is_deferred_feature("mouse")).to_equal(true)
expect(smux_is_deferred_feature("key-table-compat")).to_equal(true)
expect(smux_is_deferred_feature("tmux-conf")).to_equal(true)
expect(smux_is_deferred_feature("control-mode")).to_equal(true)
expect(smux_is_deferred_feature("split-pane")).to_equal(false)
```

</details>

### NFR-007 observability

#### expose observable startup and operation counters

- expose observable startup and operation counters
   - Expected: smux_resize(session.id, window.id, pane.id, 90, 25).is_ok() is true
   - Expected: metrics.resize_count equals `1`
   - Expected: metrics.capture_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expose observable startup and operation counters")
smux_reset_for_test()
val session = smux_create_session("obs")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

expect(smux_resize(session.id, window.id, pane.id, 90, 25).is_ok()).to_equal(true)
val _capture = smux_capture(session.id, window.id, pane.id, 10)
val metrics = smux_metrics()

expect(metrics.startup_count).to_be_greater_than(0)
expect(metrics.last_startup_ns).to_be_greater_than(0u64)
expect(metrics.resize_count).to_equal(1)  # oracle: metrics.resize_count must equal 1 — authoritative contract constant
expect(metrics.capture_count).to_equal(1)  # oracle: metrics.capture_count must equal 1 — authoritative contract constant
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/tmux_simpleos_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tmux_simpleos feature spec, REQ-001 session model, REQ-002 pane-backed shells, REQ-003 attach and detach, REQ-004 split and layout, REQ-005 input and output routing, REQ-006 state query API, REQ-007 capture api, REQ-008 compatibility facing api shape, REQ-009 native first backend, REQ-010 backend swap readiness, REQ-011 explicit non fatal failure handling, REQ-012 initial scope boundary, NFR-007 observability.
- tmux_simpleos feature spec
- REQ-001 session model
- REQ-002 pane-backed shells
- REQ-003 attach and detach
- REQ-004 split and layout
- REQ-005 input and output routing
- REQ-006 state query API
- REQ-007 capture api
- REQ-008 compatibility facing api shape
- REQ-009 native first backend
- REQ-010 backend swap readiness
- REQ-011 explicit non fatal failure handling
- REQ-012 initial scope boundary
- NFR-007 observability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-011`
- `REQ-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3136cf916c8af512aeead7900862b3a6a41928e705bb2040117dc43a3432e557`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3136cf916c8af512aeead7900862b3a6a41928e705bb2040117dc43a3432e557`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3136cf916c8af512aeead7900862b3a6a41928e705bb2040117dc43a3432e557`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/system/app/simpleos/feature/tmux_simpleos_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/tmux_simpleos_spec.md (current)
findings: 3 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/tmux_simpleos_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/tmux_simpleos_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/tmux_simpleos_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
<!-- sspec-maintain:scorecard:end -->
