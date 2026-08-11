# Standalone Office Calc TUI and Semantic UI Access

> As an Office operator, I run one unique evidence campaign against `OFFICE_BINARY`, the standalone artifact produced by a Phase-3 compiler, and inspect the same Calc session through its terminal and semantic UI surfaces. `OFFICE_GATE_BINARY` executes orchestration and `SIMPLE_UI_CLIENT` drives the versioned access protocol; neither tool is the Office product or an application launch dependency. The scenarios never read a shared or prior evidence directory: one inline setup creates the run id and invokes the gate, then every scenario validates only that run's command, PTY, and protocol receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Standalone Office Calc TUI and Semantic UI Access

As an Office operator, I run one unique evidence campaign against `OFFICE_BINARY`, the standalone artifact produced by a Phase-3 compiler, and inspect the same Calc session through its terminal and semantic UI surfaces. `OFFICE_GATE_BINARY` executes orchestration and `SIMPLE_UI_CLIENT` drives the versioned access protocol; neither tool is the Office product or an application launch dependency. The scenarios never read a shared or prior evidence directory: one inline setup creates the run id and invokes the gate, then every scenario validates only that run's command, PTY, and protocol receipts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/office_cli_tui_ui_access.md |
| Plan | doc/03_plan/sys_test/office_cli_tui_ui_access.md |
| Design | doc/05_design/office_cli_tui_ui_access.md |
| Research | doc/01_research/local/office_cli_tui_ui_access.md |
| Source | `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As an Office operator, I run one unique evidence campaign against
`OFFICE_BINARY`, the standalone artifact produced by a Phase-3 compiler, and
inspect the same Calc session through its terminal and semantic UI surfaces.
`OFFICE_GATE_BINARY` executes orchestration and `SIMPLE_UI_CLIENT` drives the
versioned access protocol; neither tool is the Office product or an application
launch dependency.
The scenarios never read a shared or prior evidence directory: one inline
setup creates the run id and invokes the gate, then every scenario validates
only that run's command, PTY, and protocol receipts.

The standalone Office executable is the product under test. The evidence gate,
UI protocol client, IDE diagnostic client, and modern SSpec runner are separate
cached tools. None is compiled or bootstrapped when Office launches.

The terminal and semantic protocol attach to one Calc controller and workbook.
Actions observed through the protocol must therefore appear in the final PTY
frame, and actions entered through the terminal must remain visible through
the same semantic snapshot owner.

**Requirements:** doc/02_requirements/feature/office_cli_tui_ui_access.md
**Plan:** doc/03_plan/sys_test/office_cli_tui_ui_access.md
**Design:** doc/05_design/office_cli_tui_ui_access.md
**Research:** doc/01_research/local/office_cli_tui_ui_access.md

## Syntax

Build the narrow standalone product once with an existing Phase-3 compiler:

```text
simple native-build --entry src/app/office_cli/main.spl --entry-closure ...
```

Launch terminal Calc directly:

```text
office calc [FILE] --tui
```

Launch the same terminal session with semantic UI access:

```text
office calc [FILE] --tui --ui-access-port PORT
```

Launch the real HTML Calc grid:

```text
office calc [FILE] --gui --ui-access-port PORT
```

Run this compiled modern SSpec with separately configured artifacts:

```text
OFFICE_GATE_BINARY=... OFFICE_BINARY=... SIMPLE_UI_CLIENT=... \
SIMPLE_IDE_CLIENT=... office-sspec
```

## Examples

The primary formula workflow performs these semantic operations:

1. Select `A1`, type `6`, and commit.
2. Select `A2`, type `8`, and commit.
3. Select `B1`, type `=A1*A2`, and commit.
4. Select `C1`, type `=AVG(A1:A2)`, and commit.
5. Observe `B1 = 48` and `C1 = 7` independently.
6. Read bounded correlated history.
7. Capture the final 124x37 terminal frame.

The GUI workflow launches a second product process, opens its rendered HTML,
discovers `formula_input`, `sheet_grid`, `cell_A1`, and `cell_T30`, then proves
that a formula action and an independent post-snapshot belong to that same GUI
session.

## Evidence contract

Every campaign owns a fresh `runs/sspec_<pid>_<micros>` directory. The setup
rejects a pre-existing directory and the scenarios consume only this run.

The `exec` evidence identifies every deployed artifact by absolute path,
SHA-256 digest, and modification time. Product provenance and tool provenance
are recorded separately.

The `tui` evidence contains the raw ANSI transcript, a normalized 124x37 frame,
the child PID, clean exit status, and terminal restoration result.

The `protocol` evidence contains versioned `simple.access/v1` responses for
windows, snapshots, surface discovery, finds, actions, history, malformed
formula rejection, stale targets, missing targets, and closed-service probes.

The `gui` evidence contains the exact HTML body, initial semantic snapshot,
formula action acknowledgement, independent post-snapshot, same-session parity
receipt, process reap result, and closed-port proof.

The `perf` evidence contains startup latency, a complete warm-up sequence,
twenty warm request samples, nearest-rank p95 values, and measured Office RSS.

## Acceptance boundaries

The campaign fails when an artifact is missing, stale, seed-built, or cannot be
identified. Source scans and in-process controller calls cannot substitute for
deployed subprocess evidence.

The campaign fails when the terminal is not a real PTY, its viewport differs
from 124x37, the final frame is empty, or A1 through T30 are not represented.

The campaign fails when multiplication or the `AVG` alias is accepted without
independent observation of `48` and `7` in both semantic and terminal evidence.

Rejected actions must remain rejected after an idempotent retry. In particular,
`malformed_formula`, `stale_target`, `target_not_found`, and
`unsupported_action` cannot be replayed as successful acknowledgements.

The warm limits are startup at most two seconds, snapshot p95 at most 100 ms,
find p95 at most 25 ms, action plus independent observation p95 at most 250 ms,
and access-layer RSS delta at most 20 MiB.

History is bounded to 64 events. The earliest request must be evicted after the
campaign exceeds that bound, while the newest request/result correlations stay
available.

## Troubleshooting

If readiness fails, inspect the unique run's PTY transcript and child PID before
retrying. Never reuse an older run directory.

If an action fails, compare its expected revision with the immediately previous
snapshot or acknowledgement. Do not guess or reuse a stale revision.

If formula observation fails, inspect the action acknowledgement, independent
find receipt, post-snapshot, and final terminal frame as separate witnesses.

If cleanup fails, confirm the child was reaped, the terminal attributes were
restored, and both root and snapshot requests report `source_unavailable`.

## Operator steps

1. Set `OFFICE_BINARY` to the Phase-3-built standalone Office artifact.
2. Set `OFFICE_GATE_BINARY` and `SIMPLE_UI_CLIENT` to existing orchestration and
   protocol-client artifacts; the modern SSpec runner is independent and does
   not bootstrap the full CLI for Office launch.
3. Launch `office calc` directly under a 124x37 PTY with UI access enabled.
4. Discover `main`, edit A1, A2, B1, C1 through `simple ui` structured
   actions, then capture that same process's final terminal frame.
5. Inspect independent snapshots, history, rejection diagnostics, and captures.
6. Launch `office calc --gui`, retain the real HTML grid, and prove its action
   and snapshot use that GUI process's shared semantic session.

When `OFFICE_BINARY` is unset, the legacy unified `SIMPLE_UI_CLIENT office calc`
launch remains available for compatibility. Missing configured artifacts, a
seed-built product, a stale run id, a non-PTY capture, a server
that does not answer the public protocol, or stale evidence is a failure.

## Scenarios

### Standalone Office Calc TUI, formulas, and semantic UI access

#### should launch Calc and complete the live semantic formula workflow

- Create one unique deployed Office evidence run
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: _gate_state_count() equals `1`
- Launch Calc through the standalone Office artifact
   - Artifact capture: after_step
- List active Office windows
   - Artifact capture: after_step
- Capture the Calc semantic snapshot
   - Artifact capture: after_step
- Inspect the main Calc surface
   - Artifact capture: after_step
- Find the active cell and formula input
   - Artifact capture: after_step
- Enter source values through semantic actions
   - Artifact capture: after_step
- Enter multiplication through the formula input
   - Artifact capture: after_step
- Enter AVG through the formula input
   - Artifact capture: after_step
- Review the independent post-action snapshot
   - Artifact capture: after_step
- Review correlated access history
   - Artifact capture: after_step
- Capture the rendered Calc TUI
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: screen.split("\n").len() equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create one unique deployed Office evidence run")
val root = setup_office_cli_tui_ui_access()
expect(file_exists(root + "/suite.txt")).to_be(true)
expect(_gate_state_count()).to_equal(1)

step("Launch Calc through the standalone Office artifact")
val root = check_office_gate()
step("List active Office windows")
val windows = file_read(root + "/protocol/windows.json")
expect(windows).to_contain("simple.access/v1")
expect(windows).to_contain("main")
step("Capture the Calc semantic snapshot")
expect(file_exists(root + "/protocol/snapshot-before.json")).to_be(true)
step("Inspect the main Calc surface")
val surface = file_read(root + "/protocol/surface-main.json")
expect(surface).to_contain("simple.access/v1")
expect(surface).to_contain("main")
step("Find the active cell and formula input")
val before = file_read(root + "/protocol/snapshot-before.json")
expect(before).to_contain("simple.access/v1")
expect(before).to_contain("revision")
expect(before).to_contain("main#cell_A1")
expect(before).to_contain("main#formula_input")
expect(before).to_contain("main#confirm_edit")
step("Enter source values through semantic actions")
step("Enter multiplication through the formula input")
val b1 = file_read(root + "/protocol/find-b1.json")
expect(b1).to_contain("main#cell_B1")
expect(b1).to_contain("48")
step("Enter AVG through the formula input")
val c1 = file_read(root + "/protocol/find-c1.json")
expect(c1).to_contain("main#cell_C1")
expect(c1).to_contain("7")
step("Review the independent post-action snapshot")
val after = file_read(root + "/protocol/snapshot-after.json")
expect(after).to_contain("simple.access/v1")
expect(after).to_contain("=AVG(A1:A2)")
step("Review correlated access history")
val history = file_read(root + "/protocol/history.json")
expect(history).to_contain("simple.access/v1")
expect(history).to_contain("access_request")
expect(history).to_contain("access_result")
step("Capture the rendered Calc TUI")
expect(file_exists(root + "/tui/calc-after.ansi")).to_be(true)
expect(file_exists(root + "/tui/calc-after.txt")).to_be(true)
val receipt = file_read(root + "/suite.txt")
val screen = file_read(root + "/tui/calc-after.txt")
expect(receipt).to_contain("runtime=pure-simple-self-hosted")
expect(receipt).to_contain("capture_size=124x37")
expect(receipt).to_contain("B1_display=48")
expect(receipt).to_contain("C1_display=7")
expect(screen.split("\n").len()).to_equal(38)
expect(screen).to_contain("Simple Calc")
expect(b1).to_contain("main#cell_B1")
expect(b1).to_contain("48")
expect(c1).to_contain("main#cell_C1")
expect(c1).to_contain("7")
```

</details>

<details>
<summary>Advanced: should fail closed for invalid commands, stale targets, and unsupported actions</summary>

#### should fail closed for invalid commands, stale targets, and unsupported actions

- Create one unique deployed Office evidence run
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: _gate_state_count() equals `1`
- Inspect deployed command and runtime provenance
   - Protocol capture: after_step
- Review stale, missing, and unsupported action rejection
   - Protocol capture: after_step
- Reject a malformed formula without changing its target cell
   - Protocol capture: after_step
- Verify terminal restoration and access-service shutdown
   - Protocol capture: after_step
- Confirm one fresh run supplied every assertion
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: _gate_state_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create one unique deployed Office evidence run")
val root = setup_office_cli_tui_ui_access()
expect(file_exists(root + "/suite.txt")).to_be(true)
expect(_gate_state_count()).to_equal(1)

step("Inspect deployed command and runtime provenance")
val root = check_office_gate()
val provenance = file_read(root + "/exec/runtime-provenance.txt")
val artifact = file_read(root + "/exec/runtime-artifact.txt")
val office_artifact = file_read(root + "/exec/office-artifact.txt")
val ide_artifact = file_read(root + "/exec/ide-artifact.txt")
val office_provenance = file_read(root + "/exec/office-product-provenance.txt")
val commands = file_read(root + "/exec/commands.txt")
expect(provenance.lower().contains("bootstrap seed only")).to_be(false)
expect(artifact).to_contain("runtime_sha256=")
expect(artifact).to_contain("runtime_mtime_epoch=")
expect(office_artifact).to_contain("office_sha256=")
expect(office_artifact).to_contain("office_mtime_epoch=")
expect(ide_artifact).to_contain("ide_sha256=")
expect(ide_artifact).to_contain("ide_mtime_epoch=")
expect(office_provenance.lower().contains("bootstrap seed only")).to_be(false)
val configured_office = env_get("OFFICE_BINARY")
val expected_office_mode = if configured_office != nil and configured_office != "": "standalone" else: "unified"
expect(file_read(root + "/suite.txt")).to_contain("office_mode=" + expected_office_mode)
expect(commands).to_contain("invalid_office")
expect(commands).to_contain("invalid_ide")
expect(commands).to_contain("mode: tui")
expect(commands).to_contain("mode: gui")
step("Review stale, missing, and unsupported action rejection")
val rejections = file_read(root + "/protocol/rejections.txt")
expect(rejections).to_contain("stale_target")
expect(rejections).to_contain("target_not_found")
expect(rejections).to_contain("unsupported_action")
step("Reject a malformed formula without changing its target cell")
val malformed = file_read(root + "/protocol/malformed-rejection.txt")
val malformed_before = file_read(root + "/protocol/malformed-before.json")
val malformed_after = file_read(root + "/protocol/malformed-after.json")
expect(malformed).to_contain("malformed_formula")
expect(malformed_before).to_contain("main#cell_D1")
expect(malformed_after).to_contain("main#cell_D1")
expect(file_read(root + "/suite.txt")).to_contain("malformed_formula_no_mutation=true")
step("Verify terminal restoration and access-service shutdown")
expect(file_read(root + "/tui/calc-exit.txt")).to_contain("terminal_restored=true")
expect(file_read(root + "/protocol/service-closed.txt")).to_contain("closed=true")
step("Confirm one fresh run supplied every assertion")
expect(_gate_state_count()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: should retain bounded N1 performance and deterministic evidence</summary>

#### should retain bounded N1 performance and deterministic evidence

- Create one unique deployed Office evidence run
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: _gate_state_count() equals `1`
- Retain measured warm public-CLI NFR evidence
   - Artifact capture: after_step
- Verify bounded history and deterministic TUI evidence
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: screen.split("\n").len() equals `38`
   - Expected: _gate_state_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create one unique deployed Office evidence run")
val root = setup_office_cli_tui_ui_access()
expect(file_exists(root + "/suite.txt")).to_be(true)
expect(_gate_state_count()).to_equal(1)

step("Retain measured warm public-CLI NFR evidence")
val root = check_office_gate()
expect(file_exists(root + "/perf/warm-protocol.txt")).to_be(true)
expect(file_exists(root + "/perf/startup.txt")).to_be(true)
val warm = file_read(root + "/perf/warm-protocol.txt")
val startup = file_read(root + "/perf/startup.txt")
expect(warm).to_contain("sample_count=20")
expect(warm).to_contain("snapshot_p95_us=")
expect(warm).to_contain("find_p95_us=")
expect(warm).to_contain("action_post_p95_us=")
expect(warm).to_contain("rss_delta_kib=")
expect(warm).to_contain("rss_status=measured")
expect(startup).to_contain("startup_us=")
expect(startup).to_contain("startup_limit_us=2000000")
step("Verify bounded history and deterministic TUI evidence")
val history = file_read(root + "/protocol/history.json")
val screen = file_read(root + "/tui/calc-after.txt")
expect(history).to_contain("access_request")
expect(screen.split("\n").len()).to_equal(38)
expect(file_read(root + "/suite.txt")).to_contain("capture_size=124x37")
expect(file_read(root + "/suite.txt")).to_contain("service_port_closed=true")
expect(_gate_state_count()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: should launch the real Calc HTML grid on the shared UI access session</summary>

#### should launch the real Calc HTML grid on the shared UI access session

- Create one unique deployed Office evidence run
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: _gate_state_count() equals `1`
- Launch GUI
   - Protocol capture: after_step
- Open rendered Calc HTML
   - Protocol capture: after_step
- Discover the shared semantic surface
   - Protocol capture: after_step
- Stop GUI
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: _gate_state_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create one unique deployed Office evidence run")
val root = setup_office_cli_tui_ui_access()
expect(file_exists(root + "/suite.txt")).to_be(true)
expect(_gate_state_count()).to_equal(1)

step("Launch GUI")
val root = check_office_gate()
step("Open rendered Calc HTML")
val html = file_read(root + "/gui/root.html")
expect(html.lower()).to_contain("<!doctype html>")
expect(html).to_contain("<title>Simple Calc</title>")
expect(html).to_contain("formula_input")
expect(html).to_contain("sheet_grid")
expect(html).to_contain("cell_A1")
expect(html).to_contain("cell_T30")
step("Discover the shared semantic surface")
val gui_snapshot = file_read(root + "/gui/snapshot.json")
expect(gui_snapshot).to_contain("simple.access/v1")
expect(gui_snapshot).to_contain("main#cell_A1")
expect(gui_snapshot).to_contain("main#cell_T30")
expect(gui_snapshot).to_contain("main#formula_input")
val gui_action = file_read(root + "/gui/action-result.json")
val gui_post = file_read(root + "/gui/post-snapshot.json")
val gui_parity = file_read(root + "/gui/session-parity.txt")
expect(gui_action).to_contain("simple.access/v1")
expect(gui_post).to_contain("simple.access/v1")
expect(gui_post).to_contain("main#cell_B1")
expect(gui_post).to_contain("48")
expect(gui_parity).to_contain("same_session=true")
expect(gui_parity).to_contain("result=48")
step("Stop GUI")
val gui_exit = file_read(root + "/exec/gui-exit.txt")
expect(gui_exit).to_contain("reaped=true")
expect(gui_exit).to_contain("port_closed=true")
expect(_gate_state_count()).to_equal(1)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/office_cli_tui_ui_access.md`
- **Plan:** `doc/03_plan/sys_test/office_cli_tui_ui_access.md`
- **Design:** `doc/05_design/office_cli_tui_ui_access.md`
- **Research:** `doc/01_research/local/office_cli_tui_ui_access.md`


</details>
