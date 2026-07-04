# LLM Dashboard Evidence

- status: `pass`
- strict_live: `false`
- live_dashboard: `not_required`
- live_reason: `default_route_and_collector_evidence_only`
- live_env: `build/llm_dashboard_live/evidence.env`
- diagnostics_panel: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_panel.log`
  - log_size: `1475`
  - log_sha256: `c39097101d7e80e404943ef72c789a6aa588a5d876c5192de7f4283b5460b3c7`
- vllm_control_route: `pass` exit=`0` log=`build/llm_dashboard_evidence/vllm_control_route.log`
  - log_size: `1436`
  - log_sha256: `b428e0fe1322fb9e1567195eaf7d430a00d172ac0de0c059a0b2028f2f04a936`
- agent_dashboard: `pass` exit=`0` log=`build/llm_dashboard_evidence/agent_dashboard.log`
  - log_size: `1439`
  - log_sha256: `fdef60058eedaa581ec805b0676f50073e05c58cad8e4cc0ad8b9d1d1fffb93b`
- log_modes: `pass` exit=`0` log=`build/llm_dashboard_evidence/log_modes.log`
  - log_size: `1400`
  - log_sha256: `759fbf18cb9dc1a1b40aa9b965d9575482c1f536a21181023057827a86ece2c2`
- diagnostics_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/diagnostics_collector.log`
  - log_size: `1464`
  - log_sha256: `c6d0a7f1ad6a5ff976264a4bc67e5cfcb9c5ca60146848496749d321403e8fd7`
- tooling_collector: `pass` exit=`0` log=`build/llm_dashboard_evidence/tooling_collector.log`
  - log_size: `1461`
  - log_sha256: `d6c21bf2c8f399c73874702339e213d0b4660a45e5857bf008a1dcb948340ce6`
- surface_manifest: `build/llm_dashboard_evidence/dashboard_evidence_surface_manifest.tsv`
- surface_manifest_count: `16`
- surface_manifest_size: `2063`
- surface_manifest_sha256: `aa0b53e03be3189f45a2d7ae646a6f683a753494ce92d72795ebccf2a37c2113`
- env: `build/llm_dashboard_evidence/evidence.env`

This evidence proves the local dashboard diagnostics, vLLM control route planning, agent dashboard route, log-mode CLI, diagnostics collector, and tooling artifact collector contracts. It is not live operator-dashboard proof or live vLLM serving proof; live serving remains covered by the runtime vLLM host probe lane. Run with `--strict-live` when live dashboard evidence must pass.
