# Plan: target-neutral HIR, target-selecting MIR

Goal: one HIR (and one HIR cache entry) serves every target. HIR carries all
OS/CPU/option alternatives unresolved; MIR lowering takes a `TargetSpec`
(`MirTargetContext` + cpu features + options) and selects the arm. Target
identity lives in MIR/object cache keys only.

## Today (facts, base `origin/release/1.0.0` @ 7689e37a92a)
| Site | Layer | Resolves |
|---|---|---|
| `10.frontend/core/cfg_platform.spl:126-185` `cfg_detect_os/arch` (env: SIMPLE_NATIVE_BUILD_TARGET, SIMPLE_TARGET_OS/ARCH, OS, uname) | parse | ambient target |
| `10.frontend/core/parser_preprocessor.spl:25-29,83-262` `@when/@elif/@else/@cfg` evaluated, losing arms DELETED before parse | parse | os/arch/family/feature |
| `parser_preprocessor.spl:724` target-receipted mode + `frontend_target_cfg_receipt_v1.spl` | parse | explicit target |
| `10.frontend/core/interpreter/eval_tables.spl:151-155` `cfg_eval_key_value` | interp | runtime cfg |
| `80.driver/managed_parse_group.spl:37` parse snapshot reuse gated on host os/arch/cpu | driver/parse cache | target |
| `80.driver/driver_hir_cache.spl:157-174` `hir_cache_key` = path+source+closure+entry+env switches+codec. **No target field**, yet its input AST was cfg-stripped per target -> cross-target HIR cache aliasing hazard (scope dir partitions by lane only, `:125-131`) | HIR cache | none (bug) |
| `80.driver/driver_build/incremental.spl:663` object scope folds `cfg_guard_context_identity_v1` (os/arch/cpu/features) | object cache | target (correct place) |
| `80.driver/cache/aop_guard_eval_v1.spl:14`, `aop_match_cache_driver_v1.spl:32` | driver | host target for AOP guards |
| `30.types/_TypeLayout/layout_core.spl:297,391-409` arch -> `platform_pointer_bit_for_arch` | types (HIR typing) | pointer width |
| `30.types/platform_match.spl:14-99` `CompileTarget` / `VariantMatch` | types | platform variants |
| `20.hir/generated/hir_children.spl:31,305` `InlineAsmMatch` keeps ALL arch arms in HIR | HIR | neutral (model to copy) |
| `50.mir/_MirLowering/asm_and_targets.spl:46-160,245` asm-match arm picked from target arch/os/abi | MIR | target (model) |
| `10.frontend/core/mir/lowering.spl:22-28` `mir_target_context_from(env, cfg_detect_*)` | MIR entry | target |
| `00.common/mir_target_context.spl:3-60` `MirTargetContext` arch/os/abi/backend | MIR | TargetSpec |
| `60.mir_opt/mir_opt/target_family.spl:70`, `auto_vectorize_target.spl` | MIR opt | SIMD tier |
| `70.backend/target_presets.spl` | codegen | triple/cpu |

## Moves
1. **MIR selector (slice 1, landed with this plan):** `50.mir/mir_cfg_select.spl`
   `mir_cfg_select_arm(conds, MirTargetContext, features)` - pure, no env/globals.
2. **HIR node:** `HirCfgSelect(arms: [HirCfgArm(condition_text, body)])`, generated like
   `InlineAsmMatch`; HIR lowering emits it instead of the preprocessor deleting arms.
   Decl-level `@cfg` becomes `HirItem.cfg_condition` (all variants kept, name-mangled by arm index).
3. **Parser:** preprocessor stops evaluating in the HIR lane (keeps arms as AST
   `CfgBlock`); host-interpreter lane may keep eager eval.
4. **MIR:** lowering of `HirCfgSelect`/decl variants calls `mir_cfg_select_arm`; -2 = hard error;
   -1 with no else = arm-absent error at use site only.
5. **Cache keys:** HIR key stays target-free (now correct); parse-snapshot gate
   (`managed_parse_group.spl:37`) drops os/arch/cpu; MIR/object keys keep `cfg_guard_context_identity_v1`
   but built from the explicit TargetSpec, not env.
6. **Typing:** `usize`/`isize`/pointer sizes become symbolic `TargetWord` in HIR; size
   resolution (`layout_core.spl:409`) moves to MIR layout.

## Risk areas
- Pointer width / ABI sizes used by HIR typing and const-eval (`size_of`, struct layout asserts in `_TypeLayout/c_assert_gen.spl`).
- Name resolution across arms: two arms may declare the same symbol with different signatures; typecheck each arm, require compatible signatures for neutral callers.
- Arms referencing target-only imports must typecheck lazily (unresolved import inside a non-selected arm is not an error).
- Cache transition: until step 3 lands, the HIR key is target-blind over target-stripped input (pre-existing hazard).

## Cross-target spec
`test/01_unit/compiler/50.mir/mir_cfg_select_cross_target_spec.spl`: same arms -> i686=0,
x86_64=1, aarch64=2, riscv64=3, windows-x86_64=else. Steps 2-4 extend it to full HIR->MIR modules.

```sdn
flow:
  parse:   {cfg: kept_as_ast, target: none}
  hir:     {node: HirCfgSelect, arms: all, cache_key: [path, source, closure, codec]}
  mir:     {input: TargetSpec, select: mir_cfg_select_arm, cache_key: [hir_key, os, arch, cpu, features, options]}
  codegen: {input: TargetSpec, object_key: cfg_guard_context_identity_v1}
```
