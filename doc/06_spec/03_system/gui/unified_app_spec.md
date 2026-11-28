# Unified Headless App Lifecycle Specification

> Verifies that `HeadlessApp` and `create_backend("none", ...)` load SDN layouts, process queued UI events, expose state transitions for inspection, and stop cleanly on `UIEvent.Quit`.

<!-- sdn-diagram:id=unified_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_app_spec -> std
unified_app_spec -> app_ui_none
unified_app_spec -> app_ui_factory
unified_app_spec -> common_ui
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

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-APP-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Verified |
| Requirements | REQ-SGUI-001 |
| Plan | `doc/03_plan/sys_test/simple_gui_completion.md` |
| Design | `doc/05_design/simple_gui_completion.md` |
| Source | `test/03_system/gui/unified_app_spec.spl` |
| Updated | 2026-11-28 |

## Overview

Verifies `app.ui.none.app.HeadlessApp` and `app.ui.backend_factory.create_backend`:
- Running `examples/06_io/ui/minimal.ui.sdn` with an injected `UIEvent.Quit` completes with `Ok(true)` and increments `render_count()`.
- Running `examples/06_io/ui/demo.ui.sdn` with `FocusNext`, `InsertMode`, `NormalMode`, and `Quit` renders across events and finishes cleanly.
- Missing layout files fail closed with `Err(...)`.
- Initial state inspection verifies `NORMAL` mode, title `"Minimal"`, and theme `"glass_dark"`.
- `run_single_event` advances `focused_id` and transitions `NORMAL` <-> `INSERT` mode deterministically.
- `create_backend("none", 3000)` returns a headless `NoneBackend` capable of enqueueing and polling `UIEvent` values.
