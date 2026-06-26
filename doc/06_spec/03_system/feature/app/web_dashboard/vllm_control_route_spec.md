# vLLM Dashboard Control Route System Specification

## Purpose

This manual mirrors
`test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl`.
It verifies the authenticated web-dashboard `/api/vllm/control` route and the
embedded dashboard control panel for the vLLM runtime lane.

## Coverage

- Authenticated `GET /api/vllm/control?action=preflight` returns
  `llm_dashboard_vllm_control_panel` JSONL.
- Unauthenticated API requests fail with `401 Unauthorized`.
- Query-style `base_model`, `endpoint`, `vllm_available`, and `gpu_available`
  parameters are accepted.
- Public responses redact model ids and do not expose the internal absence
  marker.
- The dashboard HTML embeds the vLLM control panel form.
- The web route stays on the dashboard-safe collector boundary and does not
  import the live executor directly.

## Verification

Run:

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl --mode=interpreter --clean
```
