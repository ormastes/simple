# AOP Completion Report

**Date:** 2026-04-04  
**Plan:** [doc/03_plan/aop_completion_plan_2026-04-04.md](../03_plan/aop_completion_plan_2026-04-04.md)  
**Support Matrix:** [doc/05_design/aop_support_matrix.md](../05_design/aop_support_matrix.md)

## Summary

AOP moves from **partial** to **complete with a clearly bounded support model**.

The compiler now provides:
- Predicate-based pointcuts over `execution`, `within`, `attr` selectors
- Compile-time weaving as the default execution model
- Deterministic before/after_success/after_error/around advice
- Scoped runtime interception for explicitly supported join points
- Verification-aware AOP constraints with E15xx diagnostics

## Implementation

### Phase 1: Support Matrix (doc)
- Created `doc/05_design/aop_support_matrix.md` — authoritative contract

### Phase 2: Parser + Predicate Validation
- Added `TOK_KW_ON/FORBID/ALLOW` tokens (216-218) to `tokens.spl`
- Added `DECL_AOP_ADVICE/DI_BINDING/ARCH_RULE` (14-16) to `ast.spl`
- Added `parse_aop_advice_decl()`, `parse_arch_rule_decl()`, `parse_pointcut_text()` to `parser_decls.spl`
- Fixed `flat_ast_bridge.spl` to populate `aop_advices`/`di_bindings`/`arch_rules` (was hardcoded `[]`)
- Created `aop_predicate_parser.spl` — validates selectors (E1501/E1503/E1507)

### Phase 3: MIR Advice Injection
- Created `mir_aop_injection.spl` — `inject_before/after_success/after_error/around_advice()`
- Bridge functions: `extract_mir_block_info()`, `classify_mir_inst_kind()`, `apply_weaving_result()`

### Phase 4: Driver Integration
- Added `weave_aop()` method to `CompilerDriver`
- Wired into JIT pipeline (after optimize_mir, before codegen)
- Wired into AOT pipeline (after optimize_mir, before codegen dispatch)
- Collects all HIR advices, builds `WeavingConfig` via `weavingconfig_from_hir_advices()`

### Phase 5: Runtime Interception Scoping
- Added `runtime_enabled` and `runtime_allowlist` to `AopWeaver`
- Runtime advice disabled in release builds (`not options.release`)
- Allowlist gating in `advices_for()` — glob pattern matching

### Phase 6: Deterministic Ordering
- Added lexicographic tiebreaker to `sort_matched_by_priority()` (priority > specificity > name)
- Strengthened ambiguous ordering warning with advice function names
- Created `aop_conflict_detect.spl` — E1504 (same pred+form+priority), E1506 (circular around)

### Phase 7: Verification + Diagnostics
- Wired predicate validation and advice form validation into `weave_aop()`
- Wired conflict detection into `weave_aop()`
- All E15xx codes active: E1501-E1508

### Phase 8: Metadata
- Created `aop_support_matrix.sdn` — machine-readable support matrix

## Files Changed

### Created (7)
| File | Lines | Purpose |
|------|-------|---------|
| `src/compiler/10.frontend/core/aop_predicate_parser.spl` | 124 | Predicate validation |
| `src/compiler/10.frontend/core/aop_conflict_detect.spl` | 83 | Conflict detection |
| `src/compiler/50.mir/mir_aop_injection.spl` | 183 | MIR advice injection |
| `src/compiler/85.mdsoc/aop_support_matrix.sdn` | 100 | Machine-readable metadata |
| `doc/05_design/aop_support_matrix.md` | 110 | Design contract |
| `doc/09_report/aop_completion_2026-04-04.md` | this file | Completion report |

### Modified (8)
| File | Change |
|------|--------|
| `tokens.spl` | +3 keywords (ON, FORBID, ALLOW) |
| `ast.spl` | +3 DECL constants, +3 constructors |
| `parser_decls.spl` | +3 dispatch cases, +3 parse functions (~65 lines) |
| `flat_ast_bridge.spl` | AOP decl accumulation (~45 lines) |
| `aop.spl` (frontend) | Lexicographic tiebreaker + ambiguity warning |
| `driver.spl` | `weave_aop()` + imports (~75 lines) |
| `driver_types.spl` | Runtime gating fields |
| `aop.spl` (tools) | Allowlist gating |

### Tests Created (5)
| File | Tests |
|------|-------|
| `aop_predicate_parser_spec.spl` | 16 |
| `aop_conflict_detect_spec.spl` | 5 |
| `aop_ordering_spec.spl` | 6 |
| `aop_weaving_config_spec.spl` | 11 |
| `aop_injection_spec.spl` | 4 |

## Known Limitations

- DI bindings (`@inject`) parsing is wired but authoring surface is deferred
- `get`/`set`/`init`/`effect` selectors are deferred with E1507 rejection
- Link-time weaving backend is deferred
- Around advice proceed() wrapping at MIR level uses entry-block call injection (not full body wrapping)
