# Space Activation Across Modifier Events

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Browser keyboard interaction and event ordering |
| Status | Static candidate; runtime and docgen not run |
| Requirements | REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008 |
| Executable source | `test/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Evidence | Exact keyboard/click trace, pending activation owner, DOM default state, and hosted/isolated parity |

## Scenario

### should retain Space activation while Shift is pressed and released

1. **Open the same keyboard button in hosted and isolated renderers**
   - Both routes load the same visible `type=button` fixture.
   - Focus, keydown, keyup, and click listeners append to the document title.
2. **Focus both buttons through the host Tab route**
   - Tab focuses `target` through each production keyboard adapter.
   - The exact initial trace is `focus,`.
3. **Hold Space while pressing and releasing Shift on both buttons**
   - Space keydown arms `target`; Shift keydown and keyup remain ordinary
     ordered events.
   - Both pending activation owners remain `target` and the held trace is
     `focus,keydown,keydown,keyup,`.
4. **Release Space and observe ordered activation in both renderers**
   - Space keyup is followed by exactly one click.
   - Both traces are `focus,keydown,keydown,keyup,keyup,click,`, both buttons
     retain focus and `data-activated`, and pending state is empty.

## Failure Discrimination

| Observation | Failure |
|---|---|
| pending target clears after Shift | an unrelated key event stole Space press ownership |
| final trace lacks `click,` | Space keyup could not consume its still-focused press |
| click precedes final keyup | Space activation moved from keyup default timing |
| duplicate click | modifier processing re-armed or replayed activation |
| hosted and isolated traces differ | an adapter bypassed the shared BrowserSession owner |

## Traceability

| Requirement | Executable evidence | Manual evidence |
|---|---|---|
| REQ-WEB-BROWSER-005 | focused button retains Space activation across Shift events | four-step keyboard scenario and final default state |
| REQ-WEB-BROWSER-007 | exact keydown/keyup/click order and one activation | held and released trace assertions |
| REQ-WEB-BROWSER-008 | hosted and isolated adapters assert identical state and trace | parity assertions in every interaction step |

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
