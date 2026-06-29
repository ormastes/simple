# LLM Dashboard Evidence

- status: `pass`
- strict_live: `true`
- live_dashboard: `pass`
- live_reason: `dashboard_live_routes_verified`
- live_env: `build/llm_dashboard_live/evidence.env`
- diagnostics_panel: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_panel.log`
- vllm_control_route: `pass` exit=`0` log=`build/llm_dashboard_evidence/vllm_control_route.log`
- agent_dashboard: `pass` exit=`0` log=`build/llm_dashboard_evidence/agent_dashboard.log`
- log_modes: `pass` exit=`0` log=`build/llm_dashboard_evidence/log_modes.log`
- diagnostics_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_collector.log`
- tooling_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/tooling_collector.log`
- env: `build/llm_dashboard_evidence/evidence.env`

This strict live check requires a separate live dashboard evidence env with `llm_dashboard_live_status=pass`. Local route, collector, and CLI evidence alone is not live operator-dashboard completion proof.
