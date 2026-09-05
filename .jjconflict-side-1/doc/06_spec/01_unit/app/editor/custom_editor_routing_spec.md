# Custom Editor Routing Specification

> Tests covering document open routes to a registered contributes_custom_editors entry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Editor Routing Specification

## Scenarios

### document open routes to a registered contributes_custom_editors entry

#### opening a .csv document resolves the real sheets.grid custom editor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opening a .csv document resolves the real sheets.grid custom editor
   - Expected: ctrl.extension_host.custom_editor_registered("sheets") is true
   - Expected: _has_event(ctrl.extension_host, "onDidResolveCustomEditor:sheets", "sheets.grid") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opening a .csv document resolves the real sheets.grid custom editor")
var session = EditSession.new()
session.open_file("custom_editor_routing_fixture_budget.csv")
var ctrl: EditorController = EditorController.new(session)
ctrl.extension_host.activate("sheets-function-registry-demo")

# Precondition: the builtin sheets extension really is active and its
# custom editor really is registered for "sheets" -- if this were
# false the routing assertion below would be vacuous.
expect(ctrl.extension_host.custom_editor_registered("sheets")).to_equal(true)

ctrl_activate_active_language(ctrl)

expect(_has_event(ctrl.extension_host, "onDidResolveCustomEditor:sheets", "sheets.grid")).to_equal(true)
```

</details>

#### opening a .rs document (no contributed custom editor for its kind) stays on the default editor

- opening a .rs document (no contributed custom editor for its kind) stays on the default editor
   - Expected: routed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opening a .rs document (no contributed custom editor for its kind) stays on the default editor")
var session = EditSession.new()
session.open_file("custom_editor_routing_fixture_notes.rs")
var ctrl: EditorController = EditorController.new(session)

ctrl_activate_active_language(ctrl)

var routed = false
for record in ctrl.extension_host.event_log:
    if record.event.starts_with("onDidResolveCustomEditor:"):
        routed = true
expect(routed).to_equal(false)
```

</details>

#### resolve_custom_editor for an unclaimed extension's kind returns no entry (the fallback source of truth)

- resolve_custom_editor for an unclaimed extension's kind returns no entry (the fallback source of truth)
   - Expected: ctrl.extension_host.find_language_for_ext(".rs") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_custom_editor for an unclaimed extension's kind returns no entry (the fallback source of truth)")
var session = EditSession.new()
session.open_file("custom_editor_routing_fixture_notes.rs")
var ctrl: EditorController = EditorController.new(session)

# ".rs" is not registered by any builtin's contributes_languages, so
# the language index can't resolve a document_kind for it at all --
# confirming the earlier no-event assertion is because there is
# genuinely no kind to route on, not a bug that swallowed the event.
expect(ctrl.extension_host.find_language_for_ext(".rs")).to_equal("")
```

</details>

#### a resolved custom editor is observable beyond the event log -- it changes what the GUI status bar renders

- a resolved custom editor is observable beyond the event log -- it changes what the GUI status bar renders
   - Expected: state.ctrl.session.active_document().custom_editor_id equals `sheets.grid`
   - Expected: frame.status_html contains `custom-editor:sheets.grid`
   - Expected: state_plain.ctrl.session.active_document().custom_editor_id equals ``
   - Expected: frame_plain.status_html does not contain `custom-editor:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a resolved custom editor is observable beyond the event log -- it changes what the GUI status bar renders")
# Until now, onDidResolveCustomEditor fired into a void: nothing
# recorded which editor won, and nothing downstream ever read it
# back, so a .csv document rendered byte-identically to a plain-text
# one. ctrl_route_to_custom_editor now stamps the resolved editor id
# onto EditorDocument.custom_editor_id, and gui_shell_render_frame's
# status bar reads it back -- so opening a document with a
# registered custom editor now produces a genuinely different
# rendered frame, not just a different event log entry.
var session = EditSession.new()
session.open_file("custom_editor_routing_fixture_budget.csv")
var state = gui_shell_new(session)
var ctrl = state.ctrl
ctrl.extension_host.activate("sheets-function-registry-demo")
ctrl_activate_active_language(ctrl)
state.ctrl = ctrl

expect(state.ctrl.session.active_document().custom_editor_id).to_equal("sheets.grid")
val frame = gui_shell_render_frame(state)
expect(frame.status_html.contains("custom-editor:sheets.grid")).to_equal(true)

var session_plain = EditSession.new()
session_plain.open_file("custom_editor_routing_fixture_notes.rs")
var state_plain = gui_shell_new(session_plain)
var ctrl_plain = state_plain.ctrl
ctrl_activate_active_language(ctrl_plain)
state_plain.ctrl = ctrl_plain

expect(state_plain.ctrl.session.active_document().custom_editor_id).to_equal("")
val frame_plain = gui_shell_render_frame(state_plain)
expect(frame_plain.status_html.contains("custom-editor:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/editor/custom_editor_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering document open routes to a registered contributes_custom_editors entry.
- document open routes to a registered contributes_custom_editors entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `6a7fa14255fdd221df9feab765aa8093406d67354811f9f3db0bcf80a613e298`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a7fa14255fdd221df9feab765aa8093406d67354811f9f3db0bcf80a613e298`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a7fa14255fdd221df9feab765aa8093406d67354811f9f3db0bcf80a613e298`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/editor/custom_editor_routing_spec.spl
mirror: doc/06_spec/01_unit/app/editor/custom_editor_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/editor/custom_editor_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/editor/custom_editor_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/editor/custom_editor_routing_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opening a .csv document resolves the real sheets.grid custom editor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/editor/custom_editor_routing_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opening a .rs document (no contributed custom editor for its kind) stays on the default editor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/editor/custom_editor_routing_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolve_custom_editor for an unclaimed extension's kind returns no entry (the fallback source of truth)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
