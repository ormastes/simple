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
