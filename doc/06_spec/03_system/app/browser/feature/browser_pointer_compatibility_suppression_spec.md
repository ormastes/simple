# Primary Pointer Compatibility Suppression

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Browser interaction |
| Status | Static candidate; runtime and docgen not run |
| Requirements | REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008 |
| Executable source | `test/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Evidence | Exact DOM event trace through hosted and isolated-worker routes |

## Scenario

### should suppress compatibility mouse events after canceled pointerdown

1. **Open the same canceling button in hosted and isolated renderers**
   - Both routes open the same visible `type=button` fixture.
   - Its primary `pointerdown` listener records the event and calls
     `preventDefault()`.
2. **Press the primary pointer on both buttons**
   - Each route records exactly `pointerdown,`.
   - The hosted callback delta is one and both routes retain the compatibility
     suppression bit for the active press.
3. **Release the primary pointer over the original targets**
   - Each route retains `pointerup` and the same-target `click`.
   - Compatibility `mouseup` remains suppressed with `mousedown`.
4. **Observe pointer click order and suppressed compatibility mouse events**
   - The exact trace is `pointerdown,pointerup,click,` in both routes.
   - Each browser reports exactly three callbacks, no pending navigation, and
     empty pressed/suppression state after release.

## Failure Discrimination

| Observed trace | Failure |
|---|---|
| `pointerdown,mousedown,...` | canceled pointerdown did not suppress compatibility mouse down |
| `...,pointerup,mouseup,...` | suppression state was not retained through release |
| missing `pointerup` | pointer cancellation incorrectly removed the pointer event |
| missing or duplicate `click` | same-target activation changed while suppressing mouse compatibility |
| nonempty state after release | press-lifetime state leaked into the next interaction |

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-WEB-BROWSER-007 | cancellation controls compatibility event production and exact dispatch order |
| REQ-WEB-BROWSER-008 | hosted and isolated visible-button pointer/click behavior remains equivalent |

## Provenance

This page was hand-reconciled with the executable scenario because this bounded
lane explicitly forbids runtime and docgen execution. It makes no runtime PASS
claim. The executable SSpec remains the authoritative assertion source.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
