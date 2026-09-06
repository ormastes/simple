# GPU Frontend Offload Switch — TL;DR

- One switch, default **off**: `--frontend-offload=off|on|resident|auto`,
  env `SIMPLE_FRONTEND_OFFLOAD`, `simple.sdn frontend.offload` (config reader is Wave 1, GFO-005); CLI > env > config.
- Fallback policy `allow-cpu` (default) | `require-requested`, same three sources.
- Resolves into the existing `CompilerOffloadProfile` (`OffloadMode`,
  `OffloadFallbackPolicy`, `OffloadDecision`) — no new mode enum.
- Wave 0 truth: GPU parse is unimplemented, so `on` + `allow-cpu` records
  `fallback_reason=parse_mode_unimplemented` and runs the CPU oracle; `auto`
  records `auto_profile_not_implemented_wave_1` (no retained crossover evidence);
  `on` + `require-requested` fails the compile. `off` never touches GPU code.
- New pure file: `structural_contracts/frontend_offload_switch.spl`;
  driver reads env in `80.driver/driver_source_pipeline_parsing.spl`.
- Receipt: `[frontend-offload] requested= selected= reason= source=`.
- Parity: `off` and `on+allow-cpu` must yield identical `deterministic_hash`.

<!-- sdn-diagram:gpu-frontend-offload-switch-tldr -->
```sdn
inputs -> resolve_frontend_offload -> FrontendOffloadSwitch -> frontend_offload_decision -> OffloadDecision
```
