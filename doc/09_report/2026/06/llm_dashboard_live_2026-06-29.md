# LLM Dashboard Live Evidence

- status: `fail`
- reason: `dashboard_live_http_or_route_gap`
- scope: `authenticated_dashboard_route_execution`
- required_gates: `dashboard_evidence,route_spec_html,route_spec_auth,route_spec_api,route_spec_side_effect,route_spec_owner,agent_spec_auth,agent_spec_render,agent_spec_prefix,server_route,server_agents_route,server_agents_render,server_boundary,server_execution,guide_live,guide_api,guide_agents,runtime_plan,live_http_authenticated_request`
- blocked_gates: `live_http_authenticated_request:missing_base_url`
- primary_blocked_gate: `live_http_authenticated_request`
- dashboard_evidence_status: `pass`
- dashboard_evidence_env: `build/llm_dashboard_live/dashboard/evidence.env`
- dashboard_evidence_env_size: `580`
- dashboard_evidence_env_sha256: `c1f2c4c83d0f9f2d7349bd5f565744042bfc149194c642b4c255550aa2ae3f14`
- dashboard_evidence_log_size: `36`
- dashboard_evidence_log_sha256: `9a43f2eacabcf33d31fed9e00a09b6ae8084248648f20969dfb8d7b632c57592`
- surface_manifest: `build/llm_dashboard_live/dashboard_live_surface_manifest.tsv`
- surface_manifest_count: `9`
- surface_manifest_size: `1111`
- surface_manifest_sha256: `053aa52eba01f120524d8fdbc03ec49aa121ae61f4889d3114c10552fa048f5b`
- live_http_env: `build/llm_dashboard_live_http/evidence.env`
- live_http_status: `fail`
- live_http_reason: `missing_base_url`
- live_http_base_url_status: `missing`
- live_http_base_url_scheme_status: `not_collected`
- live_http_auth_config_status: `fail`
- live_http_auth_source: `missing`
- live_http_timeout_seconds: `10`
- live_http_dashboard_status: `not_collected`
- live_http_control_status: `not_collected`
- live_http_surface_manifest_count: `7`
- live_http_surface_manifest_size: `863`
- live_http_surface_manifest_sha256: `6341402716daff0e13a3c0a55dcc936321afbdfc6ed3f031d8f543931e664f43`
- live_http_pass_integrity_status: `not_applicable`
- live_http_pass_integrity_reason: `missing_base_url`
- failures: `live_http_authenticated_request:missing_base_url`
- next_action: `resolve live dashboard evidence failures: live_http_authenticated_request:missing_base_url`
- env: `build/llm_dashboard_live/evidence.env`

This evidence proves authenticated dashboard route contracts through checked-in specs and source surfaces, then requires separate live HTTP evidence from `LLM_DASHBOARD_LIVE_HTTP_EVIDENCE_ENV` with `llm_dashboard_live_http_status=pass` and `llm_dashboard_live_http_pass_integrity_status=pass`. Produce that env with `scripts/check/check-llm-dashboard-live-http-evidence.shs` on a configured running dashboard host. Without that env, strict dashboard completion stays failed instead of treating route-contract checks as live operator-dashboard proof. It does not claim live vLLM serving; that remains the vLLM host strict lane.
