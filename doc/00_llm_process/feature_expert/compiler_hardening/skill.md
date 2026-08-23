# Feature Expert — `compiler_hardening`

**Created:** 2026-08-21. Covers the critical-completeness hardening lanes across
`00.common`, `10.frontend`, `20.hir`, `35.semantics`, `40.mono`, `50.mir`, `99.loader`.

## Role

Own process knowledge for making every compiler transition **total and loud**: no silent
fallbacks, no wildcard-closed critical matches, no unresolved generics past mono, no `Any`
escaping outside an unsafe capability.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Research: `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
- Design: `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md`
- Plan: `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md` (phases 0–9, waves 0–5)
- Requirements: `doc/02_requirements/language/mission_critical_profile.md` (REQ-MC-001..014, 023)
- Related: `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`

## What exists now (source entry points)

| Area | Path | Entry symbols |
|---|---|---|
| Transition model | `src/compiler/00.common/transition/` | `transition_table.spl`, `validator.spl`, `coverage_state.spl`, `check_main.spl` |
| Dynamic identity | `src/compiler/00.common/dynamic_identity/` | `freeze_universe`, `dyn_tag`, `claim_of`, `deserialize_to_dense`, `sort_persistent_ids`, `critical_admits` |
| Exhaustiveness | `src/compiler/20.hir/exhaustiveness/` | `coverage_witness_for`, `coverage_witness_code`; `20.hir/match_coverage.spl` |
| Enum attributes | `src/compiler/20.hir/hir_definitions.spl` (generated attributes on `HirEnum`) | via `35.semantics/enum_contract/` |
| Enum contracts | `src/compiler/35.semantics/enum_contract/` | `contract_model.spl`, `declaration_check.spl`, `match_check.spl`, `attribute_source.spl`, `check.spl` |
| Any escape | `src/compiler/35.semantics/any_escape/` | `any_escape_check` (`checker.spl`, `types.spl`) |
| Post-mono verify | `src/compiler/40.mono/verify/post_mono_verify.spl` | template pruning in `40.mono/monomorphize_integration.spl`, `monomorphize/type_subst.spl` |
| MIR type totality | `src/compiler/50.mir/mir_lowering_types.spl`, `_MirLoweringExpr/expr_dispatch.spl` | explicit arm per `HirTypeKind` |
| Completeness seal | `src/compiler/99.loader/completeness_seal/` | `parse_manifest_text`, `required_operations`, `missing_operations`, `missing_module_interfaces`, `seal.spl`, `axis_parse.spl` |
| Schema registry CLI | `src/app/compiler_schema/` | `main.spl`, `registry.spl`, `extract.spl`, `coverage.spl` (tests: `test/01_unit/app/compiler_schema/`) |
| FlatAst loud fallbacks | `src/compiler/10.frontend/_FlatAstBridge/{convert_nodes,module_assembly}.spl` | |

## Gates (verdict lines)

Repo convention: `PASS — <n> ... checked, ...` exit 0 / `FAIL — ...` exit 1 /
`ERROR — nothing was checked` exit 2. A 0-item run is ERROR. All have fatal `--selftest`.

| Gate | Verdict shape |
|---|---|
| `scripts/check/check-critical-wildcard-ban.shs` | `PASS — <n> site(s) checked, forbidden=<k> (baseline <k>)` — ratchet; selftest 8 fixtures |
| `scripts/check/check-compiler-transition-coverage.shs` | `PASS — <n> transition row(s) checked, missing=0 silent-fallback=0 critical-wildcard=0`; selftest `4 fixture(s) across 4 table(s)` |
| `scripts/check/check-compiler-schema-fresh.shs` | `PASS — <n> variant(s) across <k> enum(s), registry fresh` |
| `scripts/check/check-post-mono-invariants.shs` | `PASS — <n> fixture(s) checked, 0 unexpected`; selftest 4 scenarios |
| `scripts/check/check-any-escape-census.shs` | `PASS — <n> module(s) checked, <a> Any site(s), <e> escape(s), <u> unanalyzable (baseline …)` |
| `scripts/check/check-duplicate-pub-fn-names.shs` | `PASS — <n> pub fn(s) checked, <k> colliding name(s) (baseline <k>)` — measured baseline 78325 / 1423 |
| `scripts/check/check-hardening-mutation.shs` | `PASS — <n> row(s) checked, 0 missing` — mutation-kills-the-guard meta-check |

## Known gaps / bugs filed 2026-08-21

- `doc/08_tracking/bug/enum_decorators_dropped_before_hir_2026-08-21.md`
- `doc/08_tracking/bug/hir_generic_templates_unconsumed_by_mono_pass_2026-08-21.md` — OPEN; `check-post-mono-invariants.shs` PASSes on fixtures only
- `doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md` — OPEN
- `doc/08_tracking/bug/unsafe_capability_block_syntax_not_parsed_2026-08-21.md` — OPEN (blocks Phase 2 `type_erasure`)
- `doc/08_tracking/bug/standalone_hir_lowering_aborts_on_real_compiler_files_2026-08-21.md` — OPEN; blocks whole-tree census
- `doc/08_tracking/bug/declare_globals_fallback_debug_print_ungated_2026-08-21.md`
- `doc/08_tracking/bug/private_helper_name_collision_across_modules_has_2026-08-21.md`
- `doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md` — fixed, `Results: 4 total, 4 passed, 0 failed`
- `doc/08_tracking/bug/crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21.md` — wrong digest, not a crash; motivated the duplicate-pub-fn ratchet
- `doc/08_tracking/bug/nil_optional_enum_return_truthy_2026-08-21.md`, `module_global_fn_pointer_lowered_as_direct_call_2026-08-21.md`,
  `interpreter_raw_array_and_glob_import_gaps_2026-08-21.md`, `map_for_each_missing_on_dict_2026-08-21.md`,
  `ssa_alloca_value_return_admission_spec_conflict_2026-08-21.md`, `seed_helper_return_type_mistyped_as_tuple_2026-08-21.md`
- Phase 7 (seed/self-host parity) stays blocked: all four tracked stage binaries SEGV —
  `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.

## How to verify

```bash
for g in critical-wildcard-ban compiler-transition-coverage compiler-schema-fresh \
         post-mono-invariants any-escape-census duplicate-pub-fn-names hardening-mutation; do
  sh scripts/check/check-$g.shs --selftest && sh scripts/check/check-$g.shs; done
bin/simple test test/01_unit/app/compiler_schema/
```
Read the **last stdout line** for the verdict; never infer PASS from exit code alone.

## Affected layer experts

`layer_expert/{compiler_driver,mir_lowering,bootstrap,test_runner}/skill.md`.
(No `compiler_common`/`hir`/`semantics`/`mono`/`loader` layer dirs exist; those layers are
owned by this feature expert until such dirs are created.)

## Update Rule

Update this file whenever a hardening lane lands, a gate's verdict shape changes, a baseline
file is regenerated, or a 2026-08-21 bug above is closed.

## Mission-critical alloc-diagnostic config (2026-08-23)

- Module: `src/compiler/00.common/mission_critical/alloc_diagnostic_config.spl`
  (`McAllocDiagnosticConfig`, `parse_alloc_allowances`, env
  `SIMPLE_MC_ALLOC_ALLOW`). Zero `use` lines, zero module state — same
  discipline as `00.common/assurance/policy_names.spl`.
- Applied by `35.semantics/noalloc_checker.spl`'s new
  `check_steady_state_gate_with_config` / `steady_state_findings`;
  `check_steady_state_gate` is unchanged and delegates with the empty default.
- It is a SCOPED, JUSTIFIED opt-out, never a global off-switch: allowances name
  individual symbols (or dot-bounded module prefixes) with a mandatory reason,
  and suppressed findings are still reported as `allowed[steady-state]`.
- Reminder for future work: the steady-state gate is still LATENT (no production
  call site — see `flight_rules.spl:295`, `effect_verifier.spl:376`).
- Guide: `doc/07_guide/language/mission_critical_alloc_diagnostic_config.md`.
- Spec: `test/01_unit/compiler/semantics/mission_critical_alloc_config_spec.spl`.
