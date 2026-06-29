# LLM Dashboard Evidence

- status: `pass`
- strict_live: `false`
- live_dashboard: `not_required`
- live_reason: `default_route_and_collector_evidence_only`
- live_env: `build/llm_dashboard_live/evidence.env`
- diagnostics_panel: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_panel.log`
- vllm_control_route: `pass` exit=`0` log=`build/llm_dashboard_evidence/vllm_control_route.log`
- log_modes: `pass` exit=`0` log=`build/llm_dashboard_evidence/log_modes.log`
- diagnostics_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_collector.log`
- tooling_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/tooling_collector.log`
- env: `build/llm_dashboard_evidence/evidence.env`

This evidence proves the local dashboard diagnostics, vLLM control route planning, log-mode CLI, diagnostics collector, and tooling artifact collector contracts. It is not live operator-dashboard proof or live vLLM serving proof; live serving remains covered by the runtime vLLM host probe lane. Run with `--strict-live` when live dashboard evidence must pass.
