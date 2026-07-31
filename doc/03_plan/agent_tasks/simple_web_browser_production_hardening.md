# Simple Web Browser Production Hardening Agent Plan

## Final Coordination State

Merge owner and final reviewer: `/root`.

Wave 1's six implementation lanes remain landed. Wave 2 adds five pushed
lanes. All eleven lanes have independent static `ACCEPT` verdicts covering
scoped diff review, interface/spec/manual consistency, exact evidence oracles,
and the absence of placeholders. They do not claim runtime or SPipe execution.

| Wave | Landed lane | Final pushed hash | Independent review |
|---|---|---|---|
| 1 | RTL flex main axis | `cde0610d8a1` | Static `ACCEPT` |
| 1 | Timer/rAF cancellation domains | `e0a3fa88794` | Static `ACCEPT` |
| 1 | Checkable controls | `2316334812e` | Static `ACCEPT` |
| 1 | Script history traversal | `fea006b874f` | Static `ACCEPT` |
| 1 | CSP `form-action` | `b100fa66454` | Static `ACCEPT` |
| 1 | Linear bounded DOM serializer | `66ee14e8b2d` | Static `ACCEPT` |
| 2 | Sandboxed form top navigation | `c510498be2f` | Static `ACCEPT` |
| 2 | Equal-`innerHTML` animation restart | `2c94266e866` | Static `ACCEPT` |
| 2 | Bounded Grid stretch | `b6dbe39e8ea` | Static `ACCEPT` |
| 2 | Animation per-frame indexing | `b35f319697c` | Static `ACCEPT` |
| 2 | Canonical Go control | `9812bb073aa` | Static `ACCEPT` |

No accepted lane contains `pass_todo`, unconditional placeholder assertions,
empty scenario bodies, or fail-fast placeholders left as successful evidence.
There are no outstanding candidate hashes or pending review states for these
eleven lanes. The separate essential-runner candidate was rejected as described
below and is not part of the landed set.

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

### Sandboxed form top navigation — `c510498be2f`

- Canonical interfaces: `BrowserSession._submit_dom_form` combines
  `BeDomEventDispatch.default_action_allowed`,
  `BrowserSession.csp_sandbox_policy.allow_forms`,
  `BrowserSession.csp_sandbox_policy.allow_top_navigation`,
  `browser_form_submission`, `browser_csp_form_action_allows`, and
  `BrowserSession._begin_network_navigation_with_form_action_policy`. A denied
  top navigation reports `CSP sandbox blocked top navigation` and leaves the
  canonical WebIR, Draw IR, and pixels stable.
- Manual steps, exactly: `Resolve the HTTPS destination`; `Validate the
  authenticated peer`; `Apply redirect and sandbox policy`; `Render only the
  authorized response`.
- Bounded scope: a local typed HTTPS fixture proves `allow-forms` alone is
  denied and `allow-forms allow-top-navigation` submits the exact POST.
  TLS/HSTS/protocol runtime and the previously landed `form-action` behavior
  remain outside this lane.

### Equal-`innerHTML` animation restart — `2c94266e866`

- Canonical interfaces: `BrowserSession._replace_current_body_children` and
  the runtime bridge fields `host_body_inner_html_dirty`,
  `host_body_text_content_dirty`, and `host_dom_mutation_generation` derive
  `body_changed` and `bridge_changed`, then call
  `BrowserSession._mark_css_animation_reconcile(body_changed or
  bridge_changed)`. Ordinary class/style mutation retains the animation epoch;
  equal `document.body.innerHTML` replacement creates new descendant identity
  and restarts its animation.
- Manual steps, exactly: `Register the browser callback`; `Advance the
  monotonic browser clock`; `Dispatch events and animation frames`; `Observe
  updated canonical Draw IR pixels and released resources`.

### Bounded Grid stretch — `b6dbe39e8ea`

- Canonical interfaces: `Style.height_auto` and
  `Style.align_items_authored` propagate through `apply_grid_decls`,
  `_tag_defaults_without_metadata`, and `tag_defaults`; layout uses
  `effective_item_align`, `grid_item_is_replaced`,
  `style_with_height_without_grid_fields`, `style_with_height`, and
  `grid_stretch_outer_h`.
- Manual steps, exactly: `Parse the styled HTML fixture`; `Resolve semantic
  layout and computed style`; `Emit canonical Draw IR`; `Render exact Engine2D
  pixels`.
- Bounded CSSWG scope: a non-replaced item with automatic block size, one
  explicit pixel row, effective `normal`/`stretch`, and no block-axis auto
  margins. Spans, implicit-row stretch, intrinsic/flexible tracks, replaced
  elements, auto-margin distribution, non-start alignment positioning, and
  full CSS Grid/WPT parity are excluded. The earlier runtime-seed invocation is
  diagnostic only and is not a qualified `PASS`.

### Animation per-frame indexing — `b35f319697c`

- Canonical interfaces: `_SimpleWebAnimationFrameIndex` owns
  `keyframes_by_name` and `instances_by_target`;
  `_SimpleWebAnimationApplyResult` exposes `styles` and
  `property_work_count`; `_apply_css_animations` uses per-frame
  `underlying_by_property: Dict<text, bool>` and
  `declaration_fragments.join(";")`. The count flows through
  `SimpleWebLayoutDrawIrResult.animation_property_work_count` and
  `simple_web_layout_rerender_retained`.
- Manual steps, exactly: `Load the bounded browser fixture`; `Exercise repeated
  navigation animation and events`; `Measure retained state and work growth`;
  `Prove stable Draw IR output within the resource ceiling`.
- The bounded oracle proves property work of `16 * 2` and `32 * 2` rather than
  the previous `376` and `1520`, zero retained paint-only work, and stable
  composition, pixels, and resources.

### Canonical Go control — `9812bb073aa`

- Canonical interfaces: `BrowserSession.activate_address`,
  `hosted_browser_process_activate_address`,
  `browser_renderer_chrome_encode`/`browser_renderer_action_decode`, and
  `HostedBrowserRendererWorkerSession._dispatch_chrome` keep Go and Enter on
  the hosted-process navigation owner. Geometry and hit-testing use
  `shared_wm_browser_toolbar_control_at`,
  `shared_wm_browser_address_width`, and
  `WM_BROWSER_ADDRESS_MIN_WIDTH`; accessibility order is Go, Address, Title
  with the canonical enabled state.
- Manual steps, exactly: `Open the production browser chrome`; `Enter and
  activate the destination`; `Use Home Bookmark Stop and Reload`; `Observe
  canonical history controls and rendered document`.

## Essential Runner Lane — Stopped at Cycle 3 of 3

Stage 3 at `64585a28…` reached phase 3, then terminated with `SIGSEGV` while
lowering `std.cli.log_modes`. It produced no candidate binary and no usable
cache. Consequently the runner, ABI, and SPipe execution remain unproved.

Candidate `3f3e0bd59963766e320289d96803ab1d3dcae44b` was rejected and remains
unpushed. It is not evidence for any accepted lane. The mandatory three-cycle
limit is exhausted, and no full bootstrap was authorized; no further retry is
planned in this wave.

## Evidence Boundary

Runtime and SPipe execution remain explicitly unclaimed. The runner crash above
prevents trustworthy execution of the target specs, and the bounded Grid seed
diagnostic does not cross that boundary. Static `ACCEPT` therefore must not be
reported as runtime `PASS`.

The overall production-hardening goal remains incomplete because the essential
runner/ABI/SPipe lane is unproved and external-host evidence is still pending:

- native Metal validation on macOS;
- native ROCm/HIP validation on an AMD ROCm host;
- native DirectX validation on Windows; and
- WebGPU validation on a host/browser with a supported adapter.

This coordination update changes only this agent-plan document. It does not
change source, runtime state, requirements, executable specs, or generated
manuals.
