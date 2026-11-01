# Generics CD / MC/DC Coverage Baseline (2026-11-01)

**Binary: seed.** `C:/dev/wt/mcdc-tool/build/cargo-target/bootstrap/simple.exe` (Rust bootstrap seed built from `release/1.0.0` in the tooling worktree). No self-hosted `bin/release/<triple>/simple` exists on the Windows host; these numbers must be re-taken on the self-hosted binary before they count toward the 90/90 exit gate.
**Base:** `origin/release/1.0.0@06ab7b36b75` (includes tooling PR #5746).
**Tool:** `sh scripts/check/cert/mcdc_module_coverage.shs instrument|run --in-place|report|restore` (design `doc/05_design/generics_coverage_mcdc.md`). Restore verified: `git status --short src` empty after each run.

## Baseline (existing specs only)

Specs: `type_infer/type_infer_correctness_spec.spl`, `type_infer/generalization_membership_index_spec.spl`, `type_infer/method_call_inference_spec.spl`, `cache/generic_tldr_view_v1_spec.spl`, `hir/generic_enum_pattern_owner_substitution_spec.spl` (all under `test/01_unit/compiler/`).

| File | Decisions | Conditions | CD % | MC/DC % |
|---|---:|---:|---:|---:|
| `src/compiler/30.types/type_infer_types.spl` | 1 | 1 | 100.0 | 100.0 |
| `src/compiler/30.types/type_infer/core.spl` | 28 | 32 | 16.7 | 15.6 |
| `src/compiler/30.types/type_infer/generalization.spl` | 9 | 11 | 55.0 | 54.5 |
| `src/compiler/30.types/type_infer/generic_calls.spl` | 27 | 35 | 0.0 | 0.0 |
| `src/compiler/20.hir/hir_lowering/pattern_enum_substitution.spl` | 27 | 36 | 38.1 | 36.1 |
| `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl` | 44 | 63 | 24.3 | 20.6 |
| **Total** | 136 | 178 | 23.2 | 21.3 |

Notes: the tool counts boolean decisions only; `match` arms are not decisions in its model, so `type_infer_types.spl` has one decision. Some specs failed during the run (exit 1); failing examples still contribute the vectors they evaluated.

## Not yet measured

Tier 2 (the 432-file grep list in `doc/03_plan/compiler/generics/generics_coverage_mcdc_plan_2026-11-01.md`) and the erased-generic MIR / generic HIR lowering files are not measured in this baseline.

## After condition-targeted specs (run `final`, seed)

Adds 6 new spec files under `test/01_unit/compiler/{type_infer,20.hir,cache}/coverage/` (291 examples, each named `file.spl:LINE cN`). 425 vectors.

| File | Decisions | Conditions | CD % | MC/DC % |
|---|---:|---:|---:|---:|
| `type_infer_types.spl` | 1 | 1 | 100.0 | 100.0 |
| `type_infer/core.spl` | 28 | 32 | 90.0 | 90.6 |
| `type_infer/generalization.spl` | 9 | 11 | 100.0 | 100.0 |
| `type_infer/generic_calls.spl` | 27 | 35 | 100.0 | 100.0 |
| `hir_lowering/pattern_enum_substitution.spl` | 27 | 36 | 96.8 | 97.2 |
| `cache_contract/generic_tldr_view_v1.spl` | 44 | 63 | 100.0 | 100.0 |
| **Total** | 136 | 178 | 97.5 | 97.8 |

Remaining gaps:
- `pattern_enum_substitution.spl:145` true outcome is unreachable (the guard at line 95 already returns Error for any unresolved actual).
- `core.spl` lines 51, 57, 66 (occurs-check loops over `Throws` effects, `Union` members, `TypeParam` bounds): reachable, not yet driven.
- `core.spl:234` example fails on current code: `unify` has no `Union` arm (fixed by PR #5747; the example now passes).
- The existing `type_infer/method_call_inference_spec.spl` fails 0/4 on the seed ("unsupported expression kind" for nested `MethodCall`); not triaged in this lane.
