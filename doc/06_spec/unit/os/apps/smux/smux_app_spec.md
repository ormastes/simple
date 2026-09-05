# Smux App Specification

> Tests covering smux app.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smux App Specification

## Scenarios

### smux app

#### creates a session from the cli entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a session from the cli entry
   - Expected: smux_run_cmd(["new", "dev"]) equals `0`
   - Expected: sessions.len() equals `1`
   - Expected: sessions[0].name equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a session from the cli entry")
smux_reset_for_test()
expect(smux_run_cmd(["new", "dev"])).to_equal(0)
val sessions = smux_list_sessions()
expect(sessions.len()).to_equal(1)
expect(sessions[0].name).to_equal("dev")
```

</details>

#### sends and captures through the active pane commands

- sends and captures through the active pane commands
   - Expected: smux_run_cmd(["new", "io"]) equals `0`
   - Expected: smux_run_cmd(["send", "io", "echo", "hi"]) equals `0`
   - Expected: smux_run_cmd(["capture", "io"]) equals `0`
   - Expected: pane.id != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and captures through the active pane commands")
smux_reset_for_test()
expect(smux_run_cmd(["new", "io"])).to_equal(0)
expect(smux_run_cmd(["send", "io", "echo", "hi"])).to_equal(0)
expect(smux_run_cmd(["capture", "io"])).to_equal(0)
val session = smux_list_sessions()[0]
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]
expect(pane.id != "").to_equal(true)
```

</details>

#### reports deferred features and exposes a filesystem app identity

- reports deferred features and exposes a filesystem app identity
   - Expected: smux_run_cmd(["deferred", "copy-mode"]) equals `0`
   - Expected: smux_remote_launch_once(42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports deferred features and exposes a filesystem app identity")
smux_reset_for_test()
expect(smux_run_cmd(["deferred", "copy-mode"])).to_equal(0)
expect(smux_help_text()).to_contain("smux deferred <feature>")
expect(smux_ready_marker(42)).to_contain(SMUX_APP_ID)
expect(smux_remote_launch_once(42)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/smux/smux_app_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering smux app.
- smux app

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `77109da1512cf2513fc2e0c91524905d29ce38a3b81b8acd178eb715773d69e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77109da1512cf2513fc2e0c91524905d29ce38a3b81b8acd178eb715773d69e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77109da1512cf2513fc2e0c91524905d29ce38a3b81b8acd178eb715773d69e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/smux/smux_app_spec.spl
mirror: doc/06_spec/unit/os/apps/smux/smux_app_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/smux/smux_app_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/smux/smux_app_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/smux/smux_app_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/smux/smux_app_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a session from the cli entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/smux/smux_app_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends and captures through the active pane commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/smux/smux_app_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports deferred features and exposes a filesystem app identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
