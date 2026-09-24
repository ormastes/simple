# compiler Layer Expert

## Role

Maintain process knowledge for the `compiler` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/compiler` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/compiler/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)
- [Collection planner: adaptive collections + typed queries (RC1 plan)](../../03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md)
- [mold-MDSOC++ linker (RC1 plan)](../../03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md)

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

- 2026-09-08 enum-pattern aliases: `interpreter_patterns.rs` resolves a
  qualified pattern's imported `EnumType` alias before comparing the runtime
  enum identity. Preserve the positive explicit-alias case and the negative
  conflicting-glob control in the focused Rust regression.

- 2026-09-05 gpu_frontend_offload: default-off frontend offload switch (`structural_contracts/frontend_offload_switch.spl`, driver gate in `80.driver/driver_source_pipeline_parsing.spl`) — see `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`.

- 2026-09-20 Stage-2 `.unwrap()` trap: in compiler code that a Stage 2 builds,
  `opt.unwrap()` on a `HirSymbol?` can bind to `Poll.unwrap` and return NULL
  (0), so `if x == nil` (sentinel 3) does not catch it. Read symbols with
  `SymbolTable.symbol_name_scalar_raw` / `symbol_defining_module_scalar_raw`
  instead (see `record_external_layout_reference`,
  `doc/08_tracking/bug/unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13.md`).
  Also avoid `use <module> as <alias>` + `alias.fn()` in the Stage 2 closure:
  `doc/08_tracking/bug/stage2_build_module_alias_call_undeclared_global_2026-09-20.md`.
