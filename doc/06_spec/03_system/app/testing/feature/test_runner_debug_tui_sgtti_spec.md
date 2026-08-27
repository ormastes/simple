# Test Runner Debug TUI SGTTI System Spec

> Validates that test-runner session-debug mode has a queryable TUI surface and that SPipe UI evidence can be captured through the shared SGTTI test interface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Debug TUI SGTTI System Spec

Validates that test-runner session-debug mode has a queryable TUI surface and that SPipe UI evidence can be captured through the shared SGTTI test interface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md |
| Plan | doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md |
| Design | doc/05_design/app/testing/test_runner_debug_tui_sgtti.md |
| Research | N/A |
| Source | `test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that test-runner session-debug mode has a queryable TUI surface and
that SPipe UI evidence can be captured through the shared SGTTI test interface.

**Requirements:** doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md
**Plan:** doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md
**Design:** doc/05_design/app/testing/test_runner_debug_tui_sgtti.md
**Research:** N/A
**TUI Captures:** build/test-artifacts/03_system/app/testing/feature/test_runner_debug_tui_sgtti/debug_tui.txt

## Syntax

The spec builds an in-process session schedule, renders it as the runner debug
TUI, writes the visible text capture, and checks the same state through
`SgttiTestDriver`.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `debug_tui.txt` | TUI capture | `build/test-artifacts/03_system/app/testing/feature/test_runner_debug_tui_sgtti/debug_tui.txt` |

## Scenarios

### test runner debug TUI through SGTTI

#### renders session debug mode as a TUI capture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders session debug mode as a TUI capture
   - Expected: _write_capture(capture) equals `0`
   - Expected: _capture_file_state(capture) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders session debug mode as a TUI capture")
val schedule = _schedule_fixture()
val model = test_runner_debug_tui_model("test/03_system", "interpreter", true, true, schedule)
val capture = test_runner_debug_tui_capture(model)

expect(_write_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
expect(capture).to_start_with("Test Runner Debug")
expect(capture).to_contain("target: test/03_system")
expect(capture).to_contain("mode: interpreter")
expect(capture).to_contain("session-enabled: true")
expect(capture).to_contain("session-debug: true")
expect(capture).to_contain("group: qemu_vm target=rv64 tests=1")
expect(capture).to_contain("group: gui_session target=headless tests=1")
```

</details>

#### exposes the debug TUI as SGTTI queryable visible state

- exposes the debug TUI as SGTTI queryable visible state
   - Expected: snapshot.access.mode equals `tui`
   - Expected: snapshot.sources[0].source_kind equals `in_process_tui`
   - Expected: driver.get_elements().unwrap().len() equals `model.lines.len() + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes the debug TUI as SGTTI queryable visible state")
val schedule = _schedule_fixture()
val model = test_runner_debug_tui_model("test/03_system", "interpreter", true, true, schedule)
val snapshot = test_runner_debug_tui_snapshot(model, 1000, 5000, 1000)
val driver = SgttiTestDriver.new(snapshot)

expect(snapshot.access.mode).to_equal("tui")
expect(snapshot.sources[0].source_kind).to_equal("in_process_tui")
expect(snapshot.sources[0].capabilities).to_contain("query_text")
assert_true(driver.check_text("root", "Test Runner Debug").unwrap())
assert_true(driver.check_text("line_8", "qemu_vm").unwrap())
assert_true(driver.check_text("line_9", "gui_session").unwrap())
expect(driver.get_elements().unwrap().len()).to_equal(model.lines.len() + 1)
```

</details>

#### keeps session-debug parser help and schedule summary aligned

- keeps session-debug parser help and schedule summary aligned
   - Expected: options.session_kind equals `qemu_vm`
   - Expected: help_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps session-debug parser help and schedule summary aligned")
val options = parse_test_args(["--session-debug", "--session-daemon", "--session-kind=qemu_vm", "test/03_system"])
val schedule = _schedule_fixture()
val model = test_runner_debug_tui_model(options.path, "interpreter", options.session_share, options.session_debug, schedule)
val summary = test_runner_debug_tui_summary(model)
val schedule_text = test_runner_debug_tui_schedule_text(schedule)
val (help_out, help_err, help_code) = _run_test_runner_help()

assert_true(options.session_debug)
assert_true(options.session_share)
assert_true(options.session_daemon)
expect(options.session_kind).to_equal("qemu_vm")
expect(summary).to_contain("debug=true")
expect(schedule_text).to_contain("Session Schedule:")
expect(help_code).to_equal(0)
expect(help_out).to_contain("--session-debug")
```

</details>

#### keeps SGTTI and debug TUI construction out of the normal runner entrypoint

- keeps SGTTI and debug TUI construction out of the normal runner entrypoint
   - Expected: _marker_state(main_source, "std.ui_test.sgtti") equals `absent`
   - Expected: _marker_state(main_source, "SgttiTestDriver") equals `absent`
   - Expected: _marker_state(main_source, "test_runner_debug_tui") equals `absent`
   - Expected: _marker_state(runner_source, "std.ui_test.sgtti") equals `absent`
   - Expected: _marker_state(runner_source, "SgttiTestDriver") equals `absent`
   - Expected: _marker_state(runner_source, "test_runner_debug_tui") equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps SGTTI and debug TUI construction out of the normal runner entrypoint")
val main_source = rt_file_read_text("src/app/test_runner_new/main.spl")
val runner_source = rt_file_read_text("src/app/test_runner_new/test_runner_main.spl")

expect(_marker_state(main_source, "std.ui_test.sgtti")).to_equal("absent")
expect(_marker_state(main_source, "SgttiTestDriver")).to_equal("absent")
expect(_marker_state(main_source, "test_runner_debug_tui")).to_equal("absent")
expect(_marker_state(runner_source, "std.ui_test.sgtti")).to_equal("absent")
expect(_marker_state(runner_source, "SgttiTestDriver")).to_equal("absent")
expect(_marker_state(runner_source, "test_runner_debug_tui")).to_equal("absent")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md`
- **Plan:** `doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md`
- **Design:** `doc/05_design/app/testing/test_runner_debug_tui_sgtti.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be68dfc1553285102a07396f035f40cb9b2ef832716db5ac65c9b79e9805508e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be68dfc1553285102a07396f035f40cb9b2ef832716db5ac65c9b79e9805508e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be68dfc1553285102a07396f035f40cb9b2ef832716db5ac65c9b79e9805508e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl
mirror: doc/06_spec/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the debug TUI as SGTTI queryable visible state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps session-debug parser help and schedule summary aligned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps SGTTI and debug TUI construction out of the normal runner entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
