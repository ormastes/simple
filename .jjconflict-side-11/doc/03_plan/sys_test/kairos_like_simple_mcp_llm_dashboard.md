# System Test Plan: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-06-28

## Scope

This plan tracks executable evidence for the assistant/dashboard lane: session
stores, timeline replay, live bridge projection, web dashboard rendering,
diagnostics panels, vLLM evidence readback, and MCP assistant control readback.

Runtime vLLM/Torch execution is out of scope here. Host-dependent runtime proof
belongs to `doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md`.

## Primary System Specs

- `test/03_system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl`
- `test/03_system/feature/app/web_dashboard/llm_agent_dashboard_spec.spl`
- `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl`
- `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl`

## Supporting Unit Specs

- `test/01_unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl`
- `test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl`
- `test/01_unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl`
- `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`
- `test/01_unit/app/llm_runtime/vllm_dashboard_live_control_spec.spl`

## Acceptance Evidence

The system specs must prove:

- dashboard routes render authenticated assistant and diagnostics views
- missing diagnostics or runtime fields render explicit public text such as
  `none` or `missing`
- web dashboard vLLM controls expose intent/runtime-owner JSONL without making
  dashboard rendering own process or HTTP side effects
- assistant dashboard readback uses persisted store/timeline evidence rather
  than hidden live state

Generated/manual spec docs must stay under `doc/06_spec` as Markdown only.
Executable `.spl` specs remain under `test/`.
