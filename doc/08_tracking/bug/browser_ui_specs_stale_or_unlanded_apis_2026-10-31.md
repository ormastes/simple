# Browser/UI system specs: remaining RED after relfix (2026-10-31)

Root cause of the largest group: merge e5b290e42a0 (release_phase3 convergence)
resolved `simple_web_html_layout_renderer.spl`, `..._paint_layout.spl` and
`hosted_browser_renderer_policy.spl` to the first parent, dropping the second
parent's fractional box lane integration and the first parent's
`hosted_browser_canonical_navigation_url` / `hosted_browser_network_error`.
Re-merged in this branch. The same merge also took the first parent for
`..._style`, `..._core`, `..._foundation`, `layout*.spl`, `simple_web_engine2d_renderer.spl`
(three-way merge of the second parent's changes still conflicts there; not redone).

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
