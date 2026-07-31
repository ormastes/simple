# Checkable Canceled-Pointer Focus Preservation

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Browser interaction and DOM event ordering |
| Status | Static candidate; runtime and docgen not run |
| Requirements | REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008 |
| Executable source | `test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Evidence | Exact event trace, focused target, checked state, and hosted/isolated parity |

## Scenario

### should preserve text focus while activating the checkbox

1. **Open the same text input and checkbox in hosted and isolated renderers**
   - Both routes load one visible text input and one visible checkbox.
   - The text input records focus loss; the checkbox records pointerdown,
     click, input, and change.
2. **Focus both text inputs through the primary pointer**
   - Each text input becomes the focused DOM target.
   - The initial exact trace is `focus,`.
3. **Activate both checkboxes after canceling their pointerdown events**
   - Each checkbox pointerdown listener records the event and calls
     `preventDefault()`.
   - Same-target release still produces click and the checkable default action.
4. **Observe checkable order and preserved text focus**
   - Both exact traces are `focus,pointerdown,click,input,change,`.
   - Neither trace contains blur or focusout, both focused targets remain
     `keep`, and both checkboxes are checked.

## Failure Discrimination

| Observation | Failure |
|---|---|
| `blur,focusout,` before `click,` | checkable pre-activation transferred focus despite canceled pointerdown |
| focused target is `choice` | default click action silently focused the checkbox |
| missing `click,input,change` | focus suppression incorrectly suppressed activation/default events |
| checkbox remains unchecked | checkable pre-activation or committed default action was lost |
| hosted and isolated traces differ | an adapter bypassed the shared BrowserSession policy |

## Traceability

| Requirement | Executable evidence | Manual evidence |
|---|---|---|
| REQ-WEB-BROWSER-007 | canceled pointerdown preserves focus while click/input/change remain ordered | four visible scenario steps and exact trace |
| REQ-WEB-BROWSER-008 | hosted and isolated renderers assert identical focus, state, and callback results | parity checks in the final observation step |

## Provenance

This page was hand-reconciled with the executable scenario because the bounded
lane forbids runtime and docgen execution. It makes no runtime PASS claim. The
executable SSpec remains the authoritative assertion source.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
