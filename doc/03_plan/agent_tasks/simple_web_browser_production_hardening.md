# Simple Web Browser Production Hardening Agent Plan

## Final Coordination State

Merge owner and final reviewer: `/root`.

Wave 1's six implementation lanes remain landed. Wave 2 adds five pushed
lanes. Wave 3 adds authenticated-transport HSTS ownership and the complete
overflow/scrollbar corrective chain. The thirteen final lanes have independent
static review verdicts covering scoped diff review, interface/spec/manual
consistency, exact evidence oracles,
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
| 3 | Hosted HSTS authenticated-transport ownership | `f081a28d6f4` | Static `REVIEW PASS`; dynamic held |
| 3 | Final overflow normalization and scrollbar policy | `4d171219e88` -> `e321b86eeae` -> `d58b333df90` -> `27d116eb2b6` | Complete chain: static `REVIEW PASS`; dynamic held |

No accepted lane contains `pass_todo`, unconditional placeholder assertions,
empty scenario bodies, or fail-fast placeholders left as successful evidence.
There are no outstanding candidate hashes or pending static review states for
the thirteen final lanes. `e321b86eeae` and `d58b333df90` were incomplete,
review-failed intermediate CSS tips; only the complete chain ending at
`27d116eb2b6` is accepted. The separate essential-runner candidate was rejected
as described below and is not part of the landed set.

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
- JavaScript owns `PendingTimerTask`; SimpleScript separately reuses the
  browser-engine `EventLoop`, whose rAF slots now carry one shared 16ms
  document-origin deadline. Staggered SimpleScript callbacks share a boundary,
  nested callbacks defer, and style mutation lowers through canonical Draw IR
  and Engine2D at 16ms rather than on an arbitrary host poll.

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

### Hosted HSTS authenticated-transport ownership — `f081a28d6f4`

- `HostedWebContentSession` now strips `Strict-Transport-Security` before every
  renderer/browser commit. Only completed runtime HTTPS `single` and CORS
  `actual` responses call `_apply_authenticated_runtime_https_hsts`; mock,
  cache, preflight, HTTP, and error paths cannot seed or renew HSTS.
- Independent static `REVIEW PASS`; the focused SSpec remains dynamically held
  on the active full-CLI build.

### Final overflow normalization and scrollbar policy — `4d171219e88` through `27d116eb2b6`

- Final-cascade `overflow-x`/`overflow-y` winners, including the two-value
  shorthand, normalize before Draw IR clipping. `scrollbar-width:none` controls
  paint without disabling the scrollport clip and remains non-inherited.
- `e321b86eeae` and `d58b333df90` were incomplete intermediate review failures;
  the corrected chain ending at `27d116eb2b6` has independent static
  `REVIEW PASS`. Its exact Draw IR and Engine2D SSpec remains dynamically held
  on the active full-CLI build.

## CORS Unsafe Request Headers — Integrated, Evidence Held

The former cross-origin unsafe-author-header bypass is repaired in
`bf7dfff029a`: a safelisted method carrying a non-safelisted author header is
preflighted before the actual request is admitted.

The real OPTIONS owner path already exists and must be completed rather than
replaced by a local header rejection:

`FetchEngine.prepare_single_hop` -> `FetchEngine.handle_cors_preflight` ->
`CorsChecker.create_preflight` -> `FetchEngine.execute_http` ->
`CorsChecker.validate_preflight_method_with_credentials`.

The shared preflight path now connects header validation. The prior rejected
draft remains rejected; the accepted repair preserves its four frozen controls:

1. preserve safelisted-method behavior without requiring an ACAM token, and
   implement ACAM `*` correctly for omitted versus included credentials;
2. enforce the 1,024-byte aggregate CORS-safelisted header-value ceiling;
3. prove the actual request was never sent, not merely that OPTIONS appeared
   first; and
4. replace the stale mirrored expectation that ACAH `*` authorizes
   `Authorization`, which always requires an explicit grant.

Frozen acceptance uses exactly four steps: `Register a cross-origin endpoint
that omits X-Admin-Action permission`; `Issue a credential-free CORS GET
carrying X-Admin-Action`; `Observe the first and only OPTIONS advertising
x-admin-action`; `Reject the fetch before the ungranted action reaches the
endpoint`. Evidence must show one total request, method `OPTIONS`,
`Access-Control-Request-Headers: x-admin-action`, zero `GET` requests, the
1,024-byte boundary, ACAM wildcard/credential parity, and explicit
`Authorization` permission. See
`doc/08_tracking/bug/browser_fetch_cors_unsafe_header_preflight_bypass_2026-07-31.md`.

Status is INTEGRATED / STATIC/EVIDENCE-HELD: source and executable-spec/manual
artifacts are accepted, but no qualified target-runtime, docgen, or SPipe PASS
is admitted while the pure-Simple runner remains unavailable.

## Essential Runner Lane — Active Qualified Full-CLI Build

The 2026-07-31 care pass used the current pure-Simple Stage 3 at
`c0d1ed…`. The prior `std.cli.log_modes` lowering boundary did not reproduce:
the focused `cli_log_modes_spec` native build completed four objects, and a
standalone minimal `parse_log_options` program ran to exit 0. Directly starting
the standalone SSpec binary then terminated with `SIGILL`; that launch bypassed
the canonical runner and is invalid as SSpec evidence.

The full CLI remained blocked after all three bounded cycles:

1. two workers timed out at 600 seconds with zero completed reusable objects;
2. eight workers reached the 1.5 GiB memory cap and exited 134 with zero
   completed reusable objects; and
3. four workers compiled 1,500 objects and reached the linker, which failed on
   missing core-C symbols.

The exact retained full-CLI logs are in the isolated
`simple-browser-go-wt` worktree:

- `build/native_probe/interpret-dispatch-care/logs/baseline-build.log`;
- `build/native_probe/interpret-dispatch-care/logs/baseline-build-cycle2.log`;
  and
- `build/native_probe/interpret-dispatch-care/logs/baseline-build-cycle3.log`.

Those three stopped attempts remain historical failures. A separate active,
fresh phase-2 pure-Simple full-CLI build now uses the retained cache and the
qualified stage2 runtime authority; it is not a full bootstrap and has not yet
produced admissible runtime evidence.

Candidate `3f3e0bd59963766e320289d96803ab1d3dcae44b` was rejected and remains
unpushed. It is not evidence for any accepted lane. No compiler edit, full
bootstrap, deployment, target-runtime PASS, or SPipe PASS has occurred. The
new qualified build is the sole active dynamic-evidence owner.

## Evidence Boundary

Runtime and SPipe execution remain explicitly unclaimed. The active full-CLI
build has not completed, the earlier standalone SSpec launch was invalid, and
the bounded Grid seed diagnostic does not cross that boundary. Static review
therefore must not be reported as runtime `PASS`.

The overall production-hardening goal remains incomplete because the essential
runner/ABI/SPipe lane is unproved and external-host evidence is still pending:

- native Metal validation on macOS;
- native ROCm/HIP validation on an AMD ROCm host;
- native DirectX validation on Windows; and
- WebGPU validation on a host/browser with a supported adapter.

This coordination update records landed source/spec commits; it does not claim
new runtime, docgen, or SPipe evidence.
