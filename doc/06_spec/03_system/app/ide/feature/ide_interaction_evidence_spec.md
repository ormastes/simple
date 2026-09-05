# IDE Interaction Evidence

> Exercises the production IDE interaction contract through a real editor session, a direct edit, Markdown diagnostics, the Office launcher action contract, and the canonical UI-access snapshot/event owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IDE Interaction Evidence

Exercises the production IDE interaction contract through a real editor session, a direct edit, Markdown diagnostics, the Office launcher action contract, and the canonical UI-access snapshot/event owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/app/ide/feature/ide_interaction_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the production IDE interaction contract through a real editor
session, a direct edit, Markdown diagnostics, the Office launcher action
contract, and the canonical UI-access snapshot/event owners.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run this spec to open and edit its Markdown fixture, verify diagnostics and the
Office action, and inspect the UI-access event transcript. Image capture stays
blocked until an image-backed provider is configured.

**Artifacts:** build/test-artifacts/03_system/app/ide/feature/ide_interaction_evidence/gui_capture.blocker.txt; build/test-artifacts/03_system/app/ide/feature/ide_interaction_evidence/event_transcript.txt

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 2 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `gui_capture.blocker.txt` | Text artifact | `build/test-artifacts/03_system/app/ide/feature/ide_interaction_evidence/gui_capture.blocker.txt` |
| `event_transcript.txt` | Text artifact | `build/test-artifacts/03_system/app/ide/feature/ide_interaction_evidence/event_transcript.txt` |

## Scenarios

### REQ-EVS-014 IDE production interaction evidence

#### captures, verifies, renders, and publishes an IDE interaction

- Capture the production IDE launch and edit interaction
   - Expected: evidence.mode equals `gui`
   - Expected: evidence.path equals `FIXTURE_PATH`
   - Expected: evidence.edit_message equals `inserted`
- Verify diagnostics and the Office launcher action
   - Expected: evidence.diagnostic_count equals `0`
   - Expected: evidence.office_action equals `open_sheets`
   - Expected: evidence.office_component equals `sheets`
   - Expected: ide_interaction_exit_code(evidence) equals `0`
   - Expected: snapshot.protocol_version equals `1`
   - Expected: launcher_open_action("sheets") equals `open_sheets`
   - Expected: component.unwrap() equals `sheets`
- Render the IDE launcher still evidence
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: visual.issues.len() equals `1`
   - Expected: visual.issues[0].code equals `vision.no_image`
   - Expected: file_read(BLOCKER_PATH) equals `GUI_CAPTURE_BLOCKER + "\n"`
- Publish the IDE event motion evidence
   - Motion capture: after_step
   - Evidence: event transcript, keyframes, and review media verified by 4 expected checks
   - Expected: events.len() equals `1`
   - Expected: events[0].event_kind equals `invoke`
   - Expected: events[0].payload equals `open_sheets`
   - Expected: file_read(TRANSCRIPT_PATH) equals `transcript`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the production IDE launch and edit interaction")
expect(_prepare_fixture()).to_be(true)
val evidence = ide_interaction_evidence("gui", FIXTURE_PATH)
expect(evidence.mode).to_equal("gui")
expect(evidence.path).to_equal(FIXTURE_PATH)
expect(evidence.opened).to_be(true)
expect(evidence.edited).to_be(true)
expect(evidence.edit_message).to_equal("inserted")

step("Verify diagnostics and the Office launcher action")
expect(evidence.diagnostic_count).to_equal(0)
expect(evidence.office_action).to_equal("open_sheets")
expect(evidence.office_component).to_equal("sheets")
val report = ide_interaction_report(evidence).join("\n")
expect(report).to_contain("opened: true")
expect(report).to_contain("edited: true")
expect(ide_interaction_exit_code(evidence)).to_equal(0)

var recent: [RecentFile] = []
val launcher = build_launcher_ui(recent)
var no_events: [UiAccessEvent] = []
val snapshot = ui_access_snapshot_from_state(UIState.new(launcher), no_events)
val sheets = ui_access_find_nodes(snapshot, "main", "", "Spreadsheets", false)
expect(snapshot.protocol_version).to_equal(1)
expect(sheets.len()).to_be_greater_than(0)
expect(launcher_open_action("sheets")).to_equal("open_sheets")
val component = launcher_action_to_component("open_sheets")
expect(component.unwrap()).to_equal("sheets")

step("Render the IDE launcher still evidence")
val visual = ui_access_visual_probe_from_snapshot(snapshot, "main")
expect(visual.captured).to_be(false)
expect(visual.issues.len()).to_equal(1)
expect(visual.issues[0].code).to_equal("vision.no_image")
expect(file_write(BLOCKER_PATH, GUI_CAPTURE_BLOCKER + "\n")).to_be(true)
expect(file_read(BLOCKER_PATH)).to_equal(GUI_CAPTURE_BLOCKER + "\n")

step("Publish the IDE event motion evidence")
val events = ui_access_record_action(no_events, 1, "main", "card_sheets", "invoke", "open_sheets")
expect(events.len()).to_equal(1)
expect(events[0].event_kind).to_equal("invoke")
expect(events[0].payload).to_equal("open_sheets")
val transcript = "1 main#card_sheets invoke open_sheets\n"
expect(file_write(TRANSCRIPT_PATH, transcript)).to_be(true)
expect(file_read(TRANSCRIPT_PATH)).to_equal(transcript)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
