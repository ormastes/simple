# LLM Dashboard Live HTTP Evidence

- status: `fail`
- reason: `missing_base_url`
- blocked_gates: `base_url`
- primary_blocked_gate: `base_url`
- pass_integrity_status: `not_applicable`
- pass_integrity_reason: `missing_base_url`
- env: `build/llm_dashboard_live_http/evidence.env`

Set `LLM_DASHBOARD_LIVE_BASE_URL` to the running dashboard origin and provide either `LLM_DASHBOARD_LIVE_AUTH_HEADER`, `LLM_DASHBOARD_LIVE_AUTH_COOKIE`, or `LLM_DASHBOARD_LIVE_COOKIE_NAME` plus `LLM_DASHBOARD_LIVE_COOKIE_VALUE`.
