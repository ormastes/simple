# TL;DR: target-neutral HIR, target-selecting MIR

- Today `@cfg/@when` arms are deleted in the parser preprocessor (`parser_preprocessor.spl:83-262`) using env-detected target (`cfg_platform.spl:126-185`); the HIR cache key (`driver_hir_cache.spl:157`) has no target field -> cross-target aliasing hazard.
- Target: HIR keeps all arms (`HirCfgSelect`, modeled on `InlineAsmMatch`); MIR picks via `mir_cfg_select_arm(conds, MirTargetContext, features)`; target only in MIR/object keys.
- Slice 1 (landed): pure MIR selector `src/compiler/50.mir/mir_cfg_select.spl` + cross-target spec (i686/x86_64/aarch64/riscv64).
- Next: HIR node, stop parser eval in HIR lane, drop target from parse-snapshot gate, symbolic pointer width.
- Risks: pointer width/ABI in HIR typing, duplicate symbols across arms, target-only imports in unselected arms.
- Full plan: `hir_target_neutral_mir_target_plan.md`.
