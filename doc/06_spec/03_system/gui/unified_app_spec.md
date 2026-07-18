# Unified Headless App Lifecycle Specification

> Verifies that `UnifiedApp` can be constructed with the headless backend, process queued events, expose state for inspection, and stop deterministically.

<!-- sdn-diagram:id=unified_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_app_spec -> std
unified_app_spec -> common
unified_app_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Headless App Lifecycle Specification

Verifies that `UnifiedApp` can be constructed with the headless backend, process queued events, expose state for inspection, and stop deterministically.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-APP-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/unified_app_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `UnifiedApp` can be constructed with the headless backend,
process queued events, expose state for inspection, and stop deterministically.

## Syntax

The app is created from an SDN layout path, backend, and `AppConfig.headless()`.

## Examples

`UnifiedApp.new(path, backend, config)` returns `Ok(app)` for valid layouts.

## Scenarios

### UnifiedApp lifecycle

<details>
<summary>Advanced: runs minimal app with Quit event and completes</summary>

#### runs minimal app with Quit event and completes _(slow)_

1. Ok

2. backend inject event

3. Ok

4. Ok
   - Expected: v is true
   - Expected: app.is_running() is false

5. Err

6. fail

7. Err

8. fail

9. Err

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        # Inject a Quit event so the run loop terminates
        backend.inject_event(UIEvent.Quit)
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("examples/06_io/ui/minimal.ui.sdn", backend, config)
        match app_result:
            Ok(app) :
                val run_result = app.run()
                match run_result:
                    Ok(v) :
                        expect(v).to_equal(true)
                        expect(app.is_running()).to_equal(false)
                    Err(e) :
                        fail("UnifiedApp run failed for minimal.ui.sdn: " + e)
            Err(e) :
                fail("UnifiedApp creation failed for minimal.ui.sdn: " + e)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: processes multiple events before quitting with demo.ui.sdn</summary>

#### processes multiple events before quitting with demo.ui.sdn _(slow)_

1. Ok

2. backend inject event

3. backend inject event

4. backend inject event

5. backend inject event

6. Ok

7. Ok
   - Expected: v is true

8. Err

9. fail

10. Err

11. fail

12. Err

13. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        # Inject FocusNext, InsertMode, NormalMode, then Quit
        backend.inject_event(UIEvent.FocusNext)
        backend.inject_event(UIEvent.InsertMode)
        backend.inject_event(UIEvent.NormalMode)
        backend.inject_event(UIEvent.Quit)
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("examples/06_io/ui/demo.ui.sdn", backend, config)
        match app_result:
            Ok(app) :
                val run_result = app.run()
                match run_result:
                    Ok(v) :
                        expect(v).to_equal(true)
                        # Backend should have rendered at least twice (initial + after events)
                        expect(backend.render_count()).to_be_greater_than(1)
                    Err(e) :
                        fail("UnifiedApp run failed for demo.ui.sdn: " + e)
            Err(e) :
                fail("UnifiedApp creation failed for demo.ui.sdn: " + e)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: returns Err for nonexistent file</summary>

#### returns Err for nonexistent file _(slow)_

1. Ok

2. Ok

3. fail

4. Err

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("nonexistent/file.ui.sdn", backend, config)
        match app_result:
            Ok(_) :
                fail("UnifiedApp creation unexpectedly succeeded for nonexistent file")
            Err(e) :
                expect(e.len()).to_be_greater_than(0)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

### UnifiedApp state inspection

<details>
<summary>Advanced: reports initial state from minimal.ui.sdn</summary>

#### reports initial state from minimal.ui.sdn _(slow)_

1. Ok

2. Ok
   - Expected: state.mode_name() equals `NORMAL`
   - Expected: state.tree.title equals `Minimal`
   - Expected: state.tree.theme equals `dark`

3. Err

4. fail

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("examples/06_io/ui/minimal.ui.sdn", backend, config)
        match app_result:
            Ok(app) :
                val state = app.current_state()
                expect(state.mode_name()).to_equal("NORMAL")
                expect(state.tree.title).to_equal("Minimal")
                expect(state.tree.theme).to_equal("dark")
            Err(e) :
                fail("UnifiedApp creation failed for minimal.ui.sdn: " + e)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: state changes after injecting events via test helper</summary>

#### state changes after injecting events via test helper _(slow)_

1. Ok

2. Ok

3. app inject event
   - Expected: s1.focused_id != initial_focus is true

4. app inject event
   - Expected: s2.mode_name() equals `INSERT`

5. app inject event
   - Expected: s3.mode_name() equals `NORMAL`

6. Err

7. fail

8. Err

9. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("examples/06_io/ui/demo.ui.sdn", backend, config)
        match app_result:
            Ok(app) :
                # Initial state
                val s0 = app.current_state()
                val initial_focus = s0.focused_id

                # Inject FocusNext via the app helper
                app.inject_event(UIEvent.FocusNext)
                val s1 = app.current_state()
                # Focus should have moved (demo has multiple widgets)
                expect(s1.focused_id != initial_focus).to_equal(true)

                # Inject InsertMode
                app.inject_event(UIEvent.InsertMode)
                val s2 = app.current_state()
                expect(s2.mode_name()).to_equal("INSERT")

                # Inject NormalMode
                app.inject_event(UIEvent.NormalMode)
                val s3 = app.current_state()
                expect(s3.mode_name()).to_equal("NORMAL")
            Err(e) :
                fail("UnifiedApp creation failed for demo.ui.sdn: " + e)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: stop helper terminates the app</summary>

#### stop helper terminates the app _(slow)_

1. Ok

2. Ok
   - Expected: app.is_running() is true

3. app stop
   - Expected: app.is_running() is false

4. Err

5. fail

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) :
        val config = AppConfig.headless()
        val app_result = UnifiedApp.new("examples/06_io/ui/minimal.ui.sdn", backend, config)
        match app_result:
            Ok(app) :
                expect(app.is_running()).to_equal(true)
                app.stop()
                expect(app.is_running()).to_equal(false)
            Err(e) :
                fail("UnifiedApp creation failed for minimal.ui.sdn: " + e)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
