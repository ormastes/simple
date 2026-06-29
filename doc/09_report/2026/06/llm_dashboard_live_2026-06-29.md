# LLM Dashboard Live Evidence

- status: `fail`
- reason: `dashboard_live_http_or_route_gap`
- scope: `authenticated_dashboard_route_execution`
- required_gates: `dashboard_evidence,route_spec_html,route_spec_auth,route_spec_api,route_spec_side_effect,route_spec_owner,agent_spec_auth,agent_spec_render,agent_spec_prefix,server_route,server_agents_route,server_agents_render,server_boundary,server_execution,guide_live,guide_api,guide_agents,runtime_plan,live_http_authenticated_request`
- blocked_gates: `live_http_authenticated_request:missing_live_http_evidence`
- primary_blocked_gate: `live_http_authenticated_request`
- dashboard_evidence_status: `pass`
- dashboard_evidence_env: `build/llm_dashboard_live/dashboard/evidence.env`
- live_http_env: `build/llm_dashboard_live_http/evidence.env`
- live_http_status: `missing`
- live_http_reason: `missing_live_http_evidence`
- live_http_dashboard_status: `not_collected`
- live_http_control_status: `not_collected`
- failures: `live_http_authenticated_request:missing_live_http_evidence`
- next_action: `resolve live dashboard evidence failures: live_http_authenticated_request:missing_live_http_evidence`
- env: `build/llm_dashboard_live/evidence.env`

This evidence proves authenticated dashboard route contracts through checked-in specs and source surfaces, then requires separate live HTTP evidence from `LLM_DASHBOARD_LIVE_HTTP_EVIDENCE_ENV` with `llm_dashboard_live_http_status=pass`. Without that env, strict dashboard completion stays failed instead of treating route-contract checks as live operator-dashboard proof. It does not claim live vLLM serving; that remains the vLLM host strict lane.
