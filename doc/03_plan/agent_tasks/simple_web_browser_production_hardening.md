# Simple Web Browser Production Hardening Agent Plan

## Final Coordination State

Merge owner and final reviewer: `/root`.

The six selected implementation lanes have independent static `ACCEPT`
verdicts and are present in the pushed history. These verdicts cover scoped
diff review, interface/spec/manual consistency, exact evidence oracles, and the
absence of placeholders. They do not claim runtime or SPipe execution.

| Selected lane | Final pushed hash | Independent review |
|---|---|---|
| RTL flex main axis | `cde0610d8a1` | Static `ACCEPT` |
| Timer/rAF cancellation domains | `e0a3fa88794` | Static `ACCEPT` |
| Checkable controls | `2316334812e` | Static `ACCEPT` |
| Script history traversal | `fea006b874f` | Static `ACCEPT` |
| CSP `form-action` | `b100fa66454` | Static `ACCEPT` |
| Linear bounded DOM serializer | `66ee14e8b2d` | Static `ACCEPT` |

No selected lane contains `pass_todo`, unconditional placeholder assertions,
empty scenario bodies, or fail-fast placeholders left as successful evidence.
There are no outstanding candidate hashes or pending review states for these
six lanes.

## Canonical Interfaces and Manual Step Vocabularies

### RTL flex main axis — `cde0610d8a1`

- Canonical interfaces: `Style.direction_rtl`, `Style.flex_direction`,
  `flex_ordered_children`, `row_flex_main_reversed`,
  `row_flex_distribution`, `rtl_row_flex_item_offset`, and
  `layout_with_style`; web layout continues to emit canonical
  `DrawIrComposition` for Engine2D pixel verification.
- Manual steps, exactly: `Parse the styled document`; `Resolve the winning
  computed style`; `Emit canonical Draw IR geometry and paint`; `Render exact
  Engine2D pixels`.

### Timer/rAF cancellation domains — `e0a3fa88794`

- Canonical interfaces: JavaScript `setTimeout`/`clearTimeout`,
  `setInterval`/`clearInterval`, `requestAnimationFrame`/
  `cancelAnimationFrame`, and `setImmediate`/`clearImmediate` lower through
  `PendingTimerTask.is_animation_frame`, `PendingTimerTask.is_immediate`,
  `PendingTimerTask.create_immediate_with_args`, and
  `JsInterpreter._native_clear_timer`.
- Manual steps, exactly: `Register the browser callback`; `Advance the
  monotonic browser clock`; `Dispatch events and animation frames`; `Observe
  updated canonical Draw IR pixels and released resources`; `Schedule
  staggered callbacks before one refresh`; `Advance to the shared frame
  boundary`; `Schedule a callback during dispatch`; `Render two aligned
  animation frames`; `Align a skipped refresh from a nonzero document origin`;
  `Keep an overflowed nested frame out of the current drain`; `Refresh
  Node-compatible animation handles exactly`; `Saturate worker wakeup after
  the drain cap`.

### Checkable controls — `2316334812e`

- Canonical interfaces: authored/live `checked` state and CSS
  `Style.accent_color` lower through `input_is_checked`,
  `input_uses_accent_color`, `_html_draw_ir_checkable_commands`, and
  `fb_input_accent_control_clip`; Draw IR metadata uses `form-control-part`,
  `checked`, and `accent-color`.
- Manual steps, exactly: `Parse the interactive HTML document`; `Resolve
  control semantics and layout`; `Emit canonical Draw IR and event metadata`;
  `Render and interact through the production browser`.

### Script history traversal — `fea006b874f`

- Canonical interfaces: script `history.back()` and `history.forward()` queue
  one `BrowserSession.pending_history_traversal_delta` and consume it through
  `_flush_runtime_side_effects_and_pump_history`,
  `_pump_pending_history_traversal`, and
  `_consume_pending_history_traversal` only after the outer loader unwinds.
- Manual steps, exactly: `Enter and commit a destination`; `Record the
  navigation entry`; `Move backward forward or stop`; `Render the restored
  document and controls`; `Commit two pages before loading a scripted
  destination`; `Request Back from the destination inline script`; `Finalize
  the destination before restoring the prior page`; `Commit pages whose
  restored scripts request opposite traversal`; `Observe the restored request
  queued after the outer Back unwinds`; `Pump the queued Forward exactly once
  on the next outer operation`; `Suspend a queued Back on an external script
  response`; `Complete the external script before restoring the prior page`;
  `Commit two pages before a suspended scripted destination`; `Queue Back
  before suspending on an external script`; `Replace the load without consuming
  its stale traversal`; `Stop one suspended traversal without navigating Back`;
  `Close another suspended traversal without navigating Back`; `Load a
  script-enabled sandbox without top-navigation`; `Keep the sandboxed page and
  clear the denied proposal`.

### CSP form-action — `b100fa66454`

- Canonical interfaces: `browser_csp_form_action_allows`,
  `browser_csp_form_action_allows_after_redirect`,
  `BrowserRequest.csp_policy`, `BrowserRequest.csp_document_url`, and
  `BrowserSession._begin_network_navigation_with_form_action_policy` preserve
  initiating-document policy through request creation and redirects.
- Manual steps, exactly: `Establish the authenticated navigation`; `Apply
  origin and sandbox policy`; `Reject invalid transport or capability state`;
  `Render only the authorized document`.

### Linear bounded DOM serializer — `66ee14e8b2d`

- Canonical interfaces: `be_dom_serialize_html`,
  `be_dom_serialize_html_for_render`, and `be_dom_serialize_children` share the
  fragment collector; diagnostics are `_be_dom_measure_html_serialization` and
  `_be_dom_html_escaped_length_within`; enforced limits are
  `BE_DOM_HTML_SERIALIZE_MAX_DEPTH`,
  `BE_DOM_HTML_SERIALIZE_MAX_FRAGMENTS`, and
  `BE_DOM_HTML_SERIALIZE_MAX_OUTPUT_LENGTH`.
- Manual steps, exactly: `Load the bounded browser fixture`; `Exercise repeated
  layout navigation or animation`; `Measure retained state and work growth`;
  `Prove stable Draw IR output within the resource ceiling`.

## Evidence Boundary

Runtime and SPipe execution remain explicitly unclaimed. The available wrapper
was identified as the Rust seed, while current-origin parser and ABI blockers
prevented trustworthy execution of these target specs; no bootstrap was
authorized. Static `ACCEPT` therefore must not be reported as runtime `PASS`.

The overall production-hardening goal remains incomplete pending external-host
evidence:

- native Metal validation on macOS;
- native ROCm/HIP validation on an AMD ROCm host;
- native DirectX validation on Windows; and
- WebGPU validation on a host/browser with a supported adapter.

This coordination update changes only this agent-plan document. It does not
change source, runtime state, requirements, executable specs, or generated
manuals.
