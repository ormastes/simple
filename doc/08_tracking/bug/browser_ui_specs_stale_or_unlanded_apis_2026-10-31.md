# Browser/UI system specs: remaining RED after relfix (2026-10-31)

Root cause of the largest group: merge e5b290e42a0 (release_phase3 convergence).
- `simple_web_html_layout_renderer.spl` and `..._paint_layout.spl` were resolved to the
  first parent, dropping the second parent's fractional box lane integration. Re-done as a
  three-way merge of those two files.
- `hosted_browser_renderer_policy.spl`: the merge applied the second parent's stale
  deletions, undoing 5ae337c915d (`hosted_browser_canonical_navigation_url`,
  `hosted_browser_network_error`, form-action fields). The restored file is byte-identical
  to the first parent: a restore, not a three-way merge. The restore moved Origin and
  preflight ownership to FetchEngine/CorsChecker (cors.spl `prepare_actual_request`,
  `build_cors_preflight`), so three examples in
  test/01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl were updated to the new
  contract: "requires cors for simple cross-origin resources", "admits sanitized
  cross-origin author headers for broker preflight", "loads ordinary cross-origin images
  without exposing a CORS fetch".
- Other files the merge took from the first parent (`style`, `core`, `foundation`,
  `layout*`, `simple_web_engine2d_renderer`) still conflict against the second parent's
  changes and were not redone.

Still RED, spec ahead of source (symbol exists in neither parent, nor origin/main):
- `BrowserRuntimeState.dom_bridge_generation` (browser_css_animation_equal_replacement)
- `BrowserRendererMessage.root_command_request_id` (field lives on
  `BrowserRendererCapabilityMessage`; 4 specs)
- `central_debug_service_v1_graph` (cdp_debug_contract_slice)
- `browser_dom_control_is_effectively_disabled` (hosted_disabled_control_pointer)
- `corpus_case31_analytic_oracle`, `run_gate`, `FontRasterizer.cache_identity_snapshot`,
  `BrowserBackend.last_draw_ir_composition_id`, `CompositorBackend.blit_pixels`

Stale specs after the route-identity refactor (8282e432b3b): `last_target_id`,
`pressed_target_id`, `text_selection_target_id`, `dispatch_dom_event(id, ...)`
must be rewritten against `*_route` APIs.

Still RED, merge not completed: web_transform_provenance, web_decimal_geometry_provenance
(0.5px box emits a command), web_opaque_box_stage1, web_corpus_case01/02.

Seed limits: `unknown extern function: rt_browser_renderer_spawn_sandboxed`;
`Cannot resolve module: plugins.backend_wasm...` / `std`.

Spec-source landmine fixed: CSS/JS braces in double-quoted literals were parsed as
interpolation (`variable margin not found`); escaped with `\{` `\}`.
