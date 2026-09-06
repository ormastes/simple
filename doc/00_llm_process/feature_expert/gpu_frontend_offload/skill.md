# Feature Expert: GPU Frontend Offload

## Role

Own process knowledge for the on/off-able GPU frontend offload: the switch that
resolves into `CompilerOffloadProfile`, its receipts, and the staged SIMD/GPU
frontend waves that follow the parser_framework landing.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Research: `doc/01_research/compiler/parser/gpu_frontend_offload_unified_parser_architecture_2026-09-01.md`,
  `doc/01_research/compiler/parser/gpu_resident_frontend_cpu_work_table_parser_unification_2026-09-01.md`,
  `doc/01_research/compiler/parser/gpu_frontend_offload_switch_gap_2026-09-05.md`
- Design: `doc/05_design/compiler/frontend/gpu_frontend_offload_switch_design.md` (+ tldr)
- Plan: `doc/03_plan/compiler/frontend/gpu_frontend_offload_plan.md`;
  agent tasks `doc/03_plan/agent_tasks/gpu_frontend_offload.md`
- Guide: `doc/07_guide/compiler/frontend/frontend_offload_switch.md` (+ tldr)
- Lane state: `.spipe/gpu_frontend_offload/state.md`
- Source: `src/compiler/00.common/structural_contracts/{offload_profile,frontend_offload_switch}.spl`,
  `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
- Specs: `test/01_unit/compiler/structural/frontend_offload_switch_spec.spl`,
  `test/01_unit/compiler/driver/frontend_offload_driver_unit_spec.spl`,
  `test/02_integration/compiler/frontend_offload_driver_spec.spl`,
  `test/01_unit/compiler/parser_auto_contextual_keyword_spec.spl` (seed `auto` named-arg fix)
- Related experts: `gpu_offload_check`, `gpu_dynamic_backend_full_offload`, `sosix_gpu`

## Constraints and handoff notes

- Mode vocabulary is the repo's `OffloadMode` (`cpu_reference | hybrid_vector_gpu | resident_gpu`); scalar/SIMD is a backend axis inside hybrid. Do not reintroduce `cpu-simd`/`gpu-verify` mode names.
- The handwritten parser is `cpu_reference` (never deleted); `gpu_parse_available` is `false` until `parser_framework` lands contracts v2 — Waves 1+ are blocked on that landing.
- Sosix host-proxy access for CUDA/Vulkan/Metal is owned by the sosix lane; Wave 4 consumes it.
- `simple.sdn frontend.offload*` is documented but unread until GFO-005 threads `ProjectContext` into the parse pipeline; the driver forwards `config: ""`.
- Warm-receipt rows come from `frontend_offload_rows`; the driver's `dtrace` line is a separate assembly over the same primitives. Both must spell modes via `offload_mode_text` — never hand-format a mode or re-derive the decision elsewhere.
- `frontend_offload_profile` still has zero production callers (plan follow-up GFO-009): it is tested, not wired.
- `auto` as a named-argument label needs a seed at or after #377 (`doc/08_tracking/bug/auto_keyword_rejected_as_named_argument_label_2026-09-05.md`, closed 2026-09-06); the deployed seed carries it.
- The deployed `bin/simple` is the Rust seed; driver-level behavior is only observable on a self-hosted binary. Unit specs prove the resolver/decision without a deploy.
- Verify one spec at a time: `SIMPLE_TIMEOUT_SECONDS=900 bin/simple test <spec> --no-session-daemon`, read the `Results:` line; `sh scripts/audit/direct-env-runtime-guard.shs --working` must stay clean.

## Update Rule

Update this file with new links and handoff notes after every pipeline stage of this feature, in the same change as the work.
