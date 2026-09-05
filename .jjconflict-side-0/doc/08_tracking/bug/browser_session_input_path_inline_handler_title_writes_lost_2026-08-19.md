# BrowserSession: input-path inline handlers run but their document.title writes are lost

- Date: 2026-08-19
- Status: OPEN
- Found while: fixing `[browser-session] ReferenceError: i is not defined / all is not defined`
  (JS engine scope-chain + missing String()/Number()/Boolean(), now fixed — see
  `test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl`)
- Blocks: `test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl`
  (still red after the engine fix; its failure message is clobbered per
  `doc/08_tracking/bug/sspec_hollow_expect_clobbers_failure_message_2026-08-19.md`)

## Symptom

Inline handlers dispatched through the TEXT-EDIT flow execute (pre-engine-fix they
even printed the ReferenceErrors, proving execution), but their `document.title`
mutations never reach `session.current_title`.

Repro (against a page whose textarea has
`onbeforeinput="document.title=document.title+'bi>'"`):

- `session.dispatch_dom_event_route(route, "beforeinput", true, true)` → title gains `bi>` (OK)
- `session._dispatch_dom_input_event_route(route, "beforeinput", true, true, Some("x"), "insertReplacementText")`
  called directly → title gains `bi>` (OK)
- `session.set_dom_text_input_route(route, "zz")` — which internally calls the exact
  same `_dispatch_dom_input_event_route` — → title UNCHANGED (BUG)
- `session.blur_dom_text_input_route(route)` — change/blur/focusout handlers run,
  title UNCHANGED (BUG)

So the loss is specific to `_apply_dom_text_edit_route` / `_blur_dom_focus_route`
composition, not to the dispatch machinery itself. Verified identical behaviour
BEFORE the JS-engine fixes (title already failed to accumulate), so this is
pre-existing, independent of the engine repair. Suspect a stale
`self.runtime_state` copy being written back after the dispatch inside these
composite flows (defect class: interpreter write-back / stale-snapshot clobber),
e.g. `_sync_runtime_body_from_dom` or `_set_dom_text_runtime_state` republishing
state captured before the dispatch.

## Repro scripts

Session-level scripts used for the bisect live at
`/tmp/claude-1000/sessfull.spl`, `/tmp/claude-1000/sessbi2.spl` (scratch; recreate
from this record if gone).
