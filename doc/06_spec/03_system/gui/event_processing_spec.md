# Headless UI Event Processing Specification

> Verifies that the headless UI app accepts keyboard, focus, resize, and quit events, updates state through the run loop, and renders without crashing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Headless UI Event Processing Specification

Verifies that the headless UI app accepts keyboard, focus, resize, and quit events, updates state through the run loop, and renders without crashing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-EVENT-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/event_processing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the headless UI app accepts keyboard, focus, resize, and quit
events, updates state through the run loop, and renders without crashing.

## Syntax

Headless tests enqueue `UIEvent` values and run until `UIEvent.Quit`.

## Examples

`HeadlessApp.new(path)` returns an app whose injected events drive rendering.

## Scenarios

### Event Processing — Keyboard Navigation

<details>
<summary>Advanced: processes KeyPress events without crashing</summary>

#### processes KeyPress events without crashing _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- processes KeyPress events without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("processes KeyPress events without crashing")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.KeyPress(key: "j"))
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_be_greater_than(0)
            Err(e) :
                fail("headless app run failed after KeyPress: " + e)
    Err(e) :
        fail("headless app creation failed for demo.ui.sdn: " + e)
```

</details>


</details>

<details>
<summary>Advanced: processes multiple navigation keys</summary>

#### processes multiple navigation keys _(slow)_

- processes multiple navigation keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("processes multiple navigation keys")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.KeyPress(key: "j"))
        app.inject_event(UIEvent.KeyPress(key: "j"))
        app.inject_event(UIEvent.KeyPress(key: "k"))
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_be_greater_than(1)
            Err(e) :
                fail("headless app run failed after navigation keys: " + e)
    Err(e) :
        fail("headless app creation failed for demo.ui.sdn: " + e)
```

</details>


</details>

### Event Processing — Focus Events

<details>
<summary>Advanced: processes FocusNext</summary>

#### processes FocusNext _(slow)_

- processes FocusNext
   - Expected: app.render_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("processes FocusNext")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.FocusNext)
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                val state_after = app.current_state()
                expect(app.render_count()).to_equal(2)
                expect(state_after.focused_id.len()).to_be_greater_than(0)
                expect(state_after.tree.all_widget_ids()).to_contain(state_after.focused_id)
            Err(e) :
                fail("headless app run failed after FocusNext: " + e)
    Err(e) :
        fail("headless app creation failed for demo.ui.sdn: " + e)
```

</details>


</details>

<details>
<summary>Advanced: processes FocusPrev</summary>

#### processes FocusPrev _(slow)_

- processes FocusPrev
   - Expected: app.render_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("processes FocusPrev")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.FocusPrev)
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                val state_after = app.current_state()
                expect(app.render_count()).to_equal(2)
                expect(state_after.focused_id.len()).to_be_greater_than(0)
                expect(state_after.tree.all_widget_ids()).to_contain(state_after.focused_id)
            Err(e) :
                fail("headless app run failed after FocusPrev: " + e)
    Err(e) :
        fail("headless app creation failed for demo.ui.sdn: " + e)
```

</details>


</details>

### Event Processing — State Changes

<details>
<summary>Advanced: tracks state after events</summary>

#### tracks state after events _(slow)_

- tracks state after events
   - Expected: app.render_count() equals `2`
   - Expected: state_after.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks state after events")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) :
        val state_before = app.current_state()
        app.inject_event(UIEvent.KeyPress(key: "j"))
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                val state_after = app.current_state()
                expect(app.render_count()).to_equal(2)
                expect(state_after.mode_name()).to_equal("NORMAL")
                expect(state_after.focused_id.len()).to_be_greater_than(0)
            Err(e) :
                fail("headless app run failed after state event: " + e)
    Err(e) :
        fail("headless app creation failed for minimal.ui.sdn: " + e)
```

</details>


</details>

### Event Processing — Quit Handling

<details>
<summary>Advanced: stops on Quit event</summary>

#### stops on Quit event _(slow)_

- stops on Quit event
   - Expected: app.render_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stops on Quit event")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_equal(1)
                expect(app.last_html().len()).to_be_greater_than(0)
            Err(e) :
                fail("headless app run failed after Quit: " + e)
    Err(e) :
        fail("headless app creation failed for minimal.ui.sdn: " + e)
```

</details>


</details>

### Event Processing — Resize Events

<details>
<summary>Advanced: handles resize without crashing</summary>

#### handles resize without crashing _(slow)_

- handles resize without crashing
   - Expected: app.render_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles resize without crashing")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) :
        app.inject_event(UIEvent.Resize(width: 120, height: 40))
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_equal(2)
                expect(app.last_html().len()).to_be_greater_than(0)
            Err(e) :
                fail("headless app run failed after Resize: " + e)
    Err(e) :
        fail("headless app creation failed for minimal.ui.sdn: " + e)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb5bf072665779e36e3e5aa82313438f23f0661c83ad0389a3261207d529cb23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb5bf072665779e36e3e5aa82313438f23f0661c83ad0389a3261207d529cb23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb5bf072665779e36e3e5aa82313438f23f0661c83ad0389a3261207d529cb23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/event_processing_spec.spl
mirror: doc/06_spec/03_system/gui/event_processing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/event_processing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/event_processing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/event_processing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/event_processing_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes KeyPress events without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/event_processing_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes multiple navigation keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/event_processing_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes FocusNext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
