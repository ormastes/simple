# GPU Frontend Offload — Staged Plan

**Date:** 2026-09-05 · **Lane:** `.spipe/gpu_frontend_offload` · **Design:**
`doc/05_design/compiler/frontend/gpu_frontend_offload_switch_design.md`
**Research:** the two 2026-09-01 docs under `doc/01_research/compiler/parser/`
plus the 2026-09-05 gap doc.

## Wave 0 — the switch (this lane, shippable now)

| ID | Task | Owner path | Exit evidence |
|---|---|---|---|
| GFO-001 | Pure resolver + profile/decision/receipt helpers | `structural_contracts/frontend_offload_switch.spl`, `__init__.spl` export | DONE 2026-09-05 — unit 16/16, sabotage bites, audit PASS |
| GFO-002 | Driver env read, cached decision, fail-closed error, dtrace + warm-receipt row | `80.driver/driver_source_pipeline_parsing.spl`, `app/cli/native_build_warm_receipt.spl` | DONE 2026-09-05 — unit 5/5, sabotage bites; seed cannot run the driver, integration probe skips honestly (self-hosted deploy needed to observe) |
| GFO-003 | CLI flags set the env vars | `src/app/cli/` arg parsing (check `git status` first — avoid peer-dirty files) | DONE 2026-09-05 — `src/app/run/main.spl` + `native_build_main.spl` env_set only |
| GFO-004 | Manual + wiki + guide | `doc/06_spec/...` (docgen, 0 stubs), `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`, `doc/07_guide/compiler/frontend/frontend_offload_switch.md` | DONE 2026-09-05 — 3 manuals `0 stubs` (generated with the main-tree docgen; the committed docgen fails `E1002 spec_kw_line`), guide + tldr, wiki |

Wave 0 must not edit any peer-dirty file (`10.frontend/treesitter/*`,
`core/lexer*.spl`, `structural/parse/contracts.spl|dialect.spl`,
`structural_adapter/`, `spipe_docgen/*`).

## Waves 1+ — blocked on peer `parser_framework` landing (contracts v2)

Mapped to the research plans (GFPU-xxx = doc 1, GPU-PARSE-xxxx = doc 2):

| Wave | Content | Blocked by |
|---|---|---|
| 1 | contracts v2 + one typed mode enum (GFPU-100..106 / GPU-PARSE-01xx); `gpu_parse_available` becomes real admission; **GFO-005** read `frontend.offload*` from `ProjectContext` (`80.driver/project.spl` `_sdn_text_at`) and forward to `driver_frontend_offload_switch` (resolver slot already tested) | peer landing |
| 2 | CPU work table + reason registry + `frontend-work` audit CLI (doc 2 §10, GFPU-800/805) | Wave 1 |
| 3 | SIMD fused UTF/classify/opaque masks over `simd_text_sffi` + `runtime_simd_utf8.c` (GFPU-500..503) | Wave 1 |
| 4 | GPU UTF/lex/structure/token/region stages on `compute_exclusive_scan` ports (GFPU-600..606) | Wave 1, gpu lanes |
| 5 | GPU local parse + Parsed HIR; CPU global names + recovery (GFPU-700..804) | Waves 2–4 |
| 6 | evidence-gated `auto` (≥1.5× median, ADR-OFF-6), resident mode (GFPU-1100..1104) | Wave 5, `gpu_mmu` |

Sosix host-proxy access for CUDA/Vulkan/Metal backends is owned by the sosix
lane; Wave 4 consumes its interface and does not design it.

## Gates

- Push tier: unit spec green via `bin/simple test <spec> --no-session-daemon`
  with a `Results:` line; no new raw `rt_*` outside owner modules
  (`scripts/audit/direct-env-runtime-guard.shs --working`).
- Wave 0 done: GFO-001..004 evidence retained in `.spipe/gpu_frontend_offload/state.md`.

<!-- sdn-diagram:gpu-frontend-offload-plan -->
```sdn
wave0: {switch, driver, cli, docs} -> shippable
wave1..6: {contracts_v2, work_table, simd, gpu_stages, local_parse, auto_resident}
blockers: [peer parser_framework landing, gpu_mmu, sosix host proxy]
```
