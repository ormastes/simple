# Compiler Feature Expert

## Role

Maintain feature-specific process knowledge for Compiler. Use this skill when work touches this feature area and keep it current as the project process produces new artifacts.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Feature Links

- [Generated wrapper traversal candidate](../../../09_report/generated_wrapper_visitor_candidate_2026-10-11.md): only carrier structs may skip their kind field; five fold wrappers corrected manually pending generator regeneration and execution.

- [Tuple record ownership candidate](../../../08_tracking/bug/enumerate_native_tuple_owner_loss_2026-10-11.md): runtime/native tuple conversion and ordinary tuple record provenance require qualified native execution; current source and fixture changes remain unqualified.
- [Windows text-hash lowering and native evidence](../../../07_guide/tooling/windows_phase2_runtime_capsule.md#text-hashing-across-runtime-providers):
  typed `text.hash()` uses tagged `rt_hash_text`; preserve user-method dispatch
  and raw `rt_str_hash` callers. MIR regressions and the native fixture cover
  distinct boundaries; authored assertions do not establish executed SPipe or
  Phase4 qualification.
- [Source](../../../src/compiler/)
- [Shared compiler source](../../../src/compiler_shared/)
- [Architecture](../../04_architecture/architecture_modules.md)
- [Compiler TODOs](../../08_tracking/todo/COMPILER_TODOS_SUMMARY.md)

## Update Rule

After research, requirements, architecture, design, implementation, verification, or release work changes this feature area, add or refresh links here so the next agent can start from the current project state.

Template: [feature_skill.md](../../template/feature_skill.md)

## Seven-plan pure-Simple handoff (2026-09-29)

See [TDD progress and remaining gates](../../../03_plan/evidence/seven_plans/parallel_pure_simple_tdd_2026-09-29.md).
Preserve the distinction between source implementation, Phase 1 diagnostics,
and native/admitted SPipe qualification. The new checks cover spill overflow,
provider terminal metadata ownership, rejected package-index markers, candidate
identity-map integrity, and truthful container constructor explanations.
The identity map is not a settlement authority. Typed container lowering and
the collision-profile regression remain open. Do not repeat unchanged green
checks or reset exhausted three-cycle allowances by renaming a task.

## Target-neutral HIR cfg select (2026-10-26)

`HirExprKind.CfgSelect` + MIR arm selection landed (step 2 slice); parser/
preprocessor emission and declaration-level arms remain. Codec specs need a
runtime registering `rt_tuple_len`. See the plan
`doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md` and the
mir_lowering / compiler layer-expert notes.
