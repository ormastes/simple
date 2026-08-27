# Headless App Specification

> 1. Ok

<!-- sdn-diagram:id=headless_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=headless_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

headless_app_spec -> std
headless_app_spec -> app
headless_app_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=headless_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Headless App Specification

## Scenarios

### HeadlessApp Loading

#### loads a valid .ui.sdn file

1. Ok
   - Expected: true is true
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        expect(true).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### returns error for nonexistent file

1. Ok
   - Expected: false is true
2. Err
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("nonexistent/path.ui.sdn")
match result:
    Ok(app) =>
        expect(false).to_equal(true)
    Err(e) =>
        expect(true).to_equal(true)
```

</details>

### HeadlessApp Running

#### performs initial render on run

1. Ok
2. Ok
3. Err
   - Expected: false is true
4. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val run_result = app.run()
        match run_result:
            Ok(_) =>
                expect(app.render_count()).to_be_greater_than(0)
            Err(e) =>
                expect(false).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### stops on Quit event

1. Ok
2. app inject event
3. Ok
   - Expected: true is true
4. Err
   - Expected: false is true
5. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) =>
                expect(true).to_equal(true)
            Err(e) =>
                expect(false).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### HeadlessApp State Transitions

#### returns current state

1. Ok
   - Expected: state.tree.title equals `Minimal`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val state = app.current_state()
        expect(state.tree.title).to_equal("Minimal")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### processes FocusNext event

1. Ok
   - Expected: new_state.tree.title equals `Minimal`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val new_state = app.run_single_event(UIEvent.FocusNext)
        expect(new_state.tree.title).to_equal("Minimal")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### processes CommandMode event

1. Ok
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val new_state = app.run_single_event(UIEvent.CommandMode)
        expect(app.render_count()).to_be_greater_than(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### HeadlessApp Render Capture

#### captures rendered HTML

1. Ok
2. app run
3. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        app.run()
        val html = app.last_html()
        expect(html.len()).to_be_greater_than(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/headless_app_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HeadlessApp Loading
- HeadlessApp Running
- HeadlessApp State Transitions
- HeadlessApp Render Capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
