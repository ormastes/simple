# Headless UI Event Processing Specification

> Verifies that the headless UI app accepts keyboard, focus, resize, and quit events, updates state through the run loop, and renders without crashing.

<!-- sdn-diagram:id=event_processing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_processing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_processing_spec -> std
event_processing_spec -> app
event_processing_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_processing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. Ok

2. app inject event

3. app inject event

4. Ok

5. Err

6. fail

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. app inject event

4. app inject event

5. app inject event

6. Ok

7. Err

8. fail

9. Err

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. app inject event

4. Ok
   - Expected: app.render_count() equals `2`

5. Err

6. fail

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. app inject event

4. Ok
   - Expected: app.render_count() equals `2`

5. Err

6. fail

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. app inject event

4. Ok
   - Expected: app.render_count() equals `2`
   - Expected: state_after.mode_name() equals `NORMAL`

5. Err

6. fail

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. Ok
   - Expected: app.render_count() equals `1`

4. Err

5. fail

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. app inject event

3. app inject event

4. Ok
   - Expected: app.render_count() equals `2`

5. Err

6. fail

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
