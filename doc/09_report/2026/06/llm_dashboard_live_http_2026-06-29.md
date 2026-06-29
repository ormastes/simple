# LLM Dashboard Live HTTP Evidence

- status: `fail`
- reason: `missing_base_url`
- required_gates: `base_url,auth_configured,unauth_api_rejected,authenticated_dashboard_html,authenticated_agents_html,authenticated_control_jsonl`
- blocked_gates: `base_url`
- primary_blocked_gate: `base_url`
- base_url_status: `missing`
- base_url_scheme_status: `not_collected`
- auth_config_status: `fail`
- auth_source: `missing`
- timeout_seconds: `10`
- surface_manifest: `build/llm_dashboard_live_http/dashboard_live_http_surface_manifest.tsv`
- surface_manifest_count: `7`
- surface_manifest_size: `863`
- surface_manifest_sha256: `6341402716daff0e13a3c0a55dcc936321afbdfc6ed3f031d8f543931e664f43`
- pass_integrity_status: `not_applicable`
- pass_integrity_reason: `missing_base_url`
- env: `build/llm_dashboard_live_http/evidence.env`

Set `LLM_DASHBOARD_LIVE_BASE_URL` to the running dashboard origin and provide either `LLM_DASHBOARD_LIVE_AUTH_HEADER`, `LLM_DASHBOARD_LIVE_AUTH_COOKIE`, or `LLM_DASHBOARD_LIVE_COOKIE_NAME` plus `LLM_DASHBOARD_LIVE_COOKIE_VALUE`.
