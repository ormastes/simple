# Native showcase DOM tab bridge gap

Status: OPEN for generic JavaScript DOM parity. An explicit native adapter now
implements tab state through the existing reducer and BrowserSession's atomic
attribute-publication API; executable interactive completion remains pending.

## Evidence

- `examples/06_io/ui/web_render_file_gui.spl` previously consumed only close
  events. It now opens the full fixture through
  `HostedWebContentSession.create_document`, dispatches ordered native pointer,
  key and committed-text events through the production hosted session, and
  submits changed BrowserSession documents on the strict renderer path.
- `src/lib/gc_async_mut/web/browser_session.spl`, `install_dom_bridge` around
  line 1812, generates `__simple_dom_matches` supporting ID, class and tag-name
  selectors only. The fixture's `[role="tab"]` and `[role="tabpanel"]` queries
  therefore return empty arrays.
- The bridge installer does not install element `setAttribute`,
  `removeAttribute`, or `focus` methods. `_bind_dom_node`, `_refresh_dom_node`
  and `_apply_dom_element` reflect id/class/value/style, but do not reflect
  `tabIndex` or `hidden`. The existing fixture uses these standard DOM APIs.

## Required repair and evidence

Generic JavaScript parity still requires these DOM surfaces in the
BrowserSession-owned bridge. The native showcase explicitly uses
`src/os/hosted/web_showcase_native_tabs.spl`: actual semantic target IDs feed
`WebShowcaseState`, then one bounded attribute batch updates aria-selected,
tabindex and hidden through BrowserSession. This preserves document generation,
unrelated DOM/form state and the shared rendering path. It does not claim that
the missing JavaScript APIs are implemented.

`test/02_integration/rendering/web_showcase_native_tabs_spec.spl` exercises the
actual complete fixture through production layout hit testing and hosted DOM
dispatch. It requires all seven panel selections, distinct focus/selection,
Home/End and Enter/Space activation. Execution remains pending the admitted
self-hosted test runtime; source inspection does not establish a PASS.

Native presented pixels, physical cursor-to-framebuffer scaling and frame
completion timestamps still require the separate 4K device/presentation check.
The runner reports successful presentation submission without claiming scanout.

## Related input correctness fix

`winit_wait_input_into` now accepts the caller's previous cursor coordinates.
Native button events contain no coordinates; resetting to zero between wait
batches could direct a click at the page origin when movement arrived in the
preceding batch. Existing callers retain the previous default behavior; the
showcase explicitly carries cursor state between waits.

## 2026-11-13 triage (UI batch B, Linux aarch64, release/1.0.0 @ 35144b7f5e93): LIVE, not closed

Source re-read: `install_dom_bridge` (`browser_session.spl:1814`) still
generates `__simple_dom_matches` for `#id`, `.class` and tag-name selectors
only. `browser_session.spl` contains no `setAttribute`, `removeAttribute`,
`focus`, `tabIndex` or `hidden` bridge surface. The generic JavaScript DOM gap
is unchanged.

Execution attempt for the native adapter evidence: `simple test
test/02_integration/rendering/web_showcase_native_tabs_spec.spl` on the Rust
seed, 16G cgroup cap, `timeout 900`. It produced no `SPEC FILE VERDICT` line
and was killed at 900 s (rc=124). No pass or fail is claimed from it; the
"executable interactive completion remains pending" line above still stands.

Not fixed in this lane. The repair needs attribute storage and reflection
added across the JS-engine host-DOM snapshot arrays and the BrowserSession
bridge (attribute selectors, `setAttribute`/`removeAttribute`, `focus`,
`tabIndex`/`hidden` reflection), which is feature work in the JS-engine and
browser-session lane, and its acceptance spec does not reach a verdict within
this host's run cap on the seed interpreter. Row stays open. Grant: a
self-hosted native test runtime, or a longer run budget for that spec.


---

## Lane disposition 2026-11-13 (p3-misc-b)

open for generic JS DOM parity per in-file status; owner: web/native bridge lane.


---
## 2026-11-13 triage — lane live-p3-l6 (Windows host, seed bin/simple.exe, base f790f7f266e)

Concur with the UI-batch-B disposition: `install_dom_bridge` still generates
`__simple_dom_matches` for `#id`/`.class`/tag selectors only, and no
setAttribute/removeAttribute/focus/tabIndex/hidden bridge surface exists in
`browser_session.spl`. The repair is cross-cutting JS-engine/browser-session
feature work whose acceptance spec does not reach a verdict within this host's
run cap on the seed interpreter. No in-lane change.
