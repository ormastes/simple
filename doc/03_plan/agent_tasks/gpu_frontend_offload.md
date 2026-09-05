# GPU Frontend Offload — Agent Tasks (Wave 0)

Worktree: `/home/yoon/dev/simple-gpu-frontend` (detached from `973f2471db1`,
`build/` symlinked to the main tree). All agents edit disjoint paths; none may
touch the peer-dirty parser_framework set.

## Frozen vocabulary (do not rename)

Types/fns: `FrontendOffloadInputs`, `FrontendOffloadSwitch`,
`parse_frontend_offload_value`, `resolve_frontend_offload`,
`frontend_offload_profile`, `frontend_offload_decision`,
`frontend_offload_parse_mode_text`, `frontend_offload_receipt_line`,
`driver_frontend_offload_switch`, `driver_frontend_offload_decision`.
Keys: `--frontend-offload`, `--frontend-offload-fallback`,
`SIMPLE_FRONTEND_OFFLOAD`, `SIMPLE_FRONTEND_OFFLOAD_FALLBACK`,
`frontend.offload`, `frontend.offload_fallback`.
Reasons: `""`, `parse_mode_unimplemented`,
`frontend_offload_required_mode_unavailable`.
Spec steps: `Resolve the frontend offload switch from CLI, env, and config`;
`Default to CPU reference when nothing is set`;
`Demote honestly when GPU parsing is unimplemented`;
`Refuse to demote under require-requested`;
`Record the offload decision receipt`.

| Agent | Owned paths | Depends | Deliverable |
|---|---|---|---|
| A — resolver | `src/compiler/00.common/structural_contracts/{frontend_offload_switch,__init__}.spl`, `test/01_unit/compiler/structural/frontend_offload_switch_spec.spl` | none | GFO-001 + unit spec green |
| B — driver/CLI | `src/compiler/80.driver/driver_source_pipeline_parsing.spl`, `src/app/cli/native_build_warm_receipt.spl`, CLI arg file (clean only), `test/02_integration/compiler/frontend_offload_driver_spec.spl` | A's signatures (frozen) | GFO-002/003 + integration probe |
| C — docs | `doc/06_spec/...` mirror, `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`, `doc/07_guide/compiler/frontend_offload_switch.md` (+tldr) | A/B file names | GFO-004, docgen `0 stubs` |

Placeholders fail with `assert(false)` / `fail(...)`. Merge order A → B → C;
root session reviews and commits in the worktree, no push while the peer lands.
