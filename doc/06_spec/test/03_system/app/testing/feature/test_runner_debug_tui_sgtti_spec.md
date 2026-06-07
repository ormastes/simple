# Test Runner Debug TUI SGTTI System Spec

> Validates that test-runner session-debug mode has a queryable TUI surface and that SPipe UI evidence can be captured through the shared SGTTI test interface.

<!-- sdn-diagram:id=test_runner_debug_tui_sgtti_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_debug_tui_sgtti_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_debug_tui_sgtti_spec -> std
test_runner_debug_tui_sgtti_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_debug_tui_sgtti_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

#### Embedded TUI Text Captures

<details>
<summary>debug_tui.txt</summary>

```text
Test Runner Debug
target: test/03_system
mode: interpreter
session-enabled: true
session-debug: true
total-tests: 3
session-groups: 2
ungrouped: 1
group: qemu_vm target=rv64 tests=1 priority=0
group: gui_session target=headless tests=1 priority=2
```

</details>

## Scenarios

### test runner debug TUI through SGTTI

#### renders session debug mode as a TUI capture

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schedule = _schedule_fixture()
val model = test_runner_debug_tui_model("test/03_system", "interpreter", true, true, schedule)
val snapshot = test_runner_debug_tui_snapshot(model, 1000, 5000, 1000)
val driver = SgttiTestDriver.new(snapshot)

expect(snapshot.access.mode).to_equal("tui")
expect(snapshot.sources[0].source_kind).to_equal("in_process_tui")
expect(snapshot.sources[0].capabilities).to_contain("query_text")
expect(driver.check_text("root", "Test Runner Debug").unwrap())
expect(driver.check_text("line_8", "qemu_vm").unwrap())
expect(driver.check_text("line_9", "gui_session").unwrap())
expect(driver.get_elements().unwrap().len()).to_equal(model.lines.len() + 1)
```

</details>

#### keeps session-debug parser help and schedule summary aligned

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = parse_test_args(["--session-debug", "--session-daemon", "--session-kind=qemu_vm", "test/03_system"])
val schedule = _schedule_fixture()
val model = test_runner_debug_tui_model(options.path, "interpreter", options.session_share, options.session_debug, schedule)
val summary = test_runner_debug_tui_summary(model)
val schedule_text = test_runner_debug_tui_schedule_text(schedule)
val (help_out, help_err, help_code) = _run_test_runner_help()

expect(options.session_debug)
expect(options.session_share)
expect(options.session_daemon)
expect(options.session_kind).to_equal("qemu_vm")
expect(summary).to_contain("debug=true")
expect(schedule_text).to_contain("Session Schedule:")
expect(help_code).to_equal(0)
expect(help_out).to_contain("--session-debug")
```

</details>

#### keeps SGTTI and debug TUI construction out of the normal runner entrypoint

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md](doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md)
- **Plan:** [doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md](doc/03_plan/sys_test/test_runner_debug_tui_sgtti.md)
- **Design:** [doc/05_design/app/testing/test_runner_debug_tui_sgtti.md](doc/05_design/app/testing/test_runner_debug_tui_sgtti.md)


</details>
