# Simple Robustness Completion Plan

**Date:** 2026-11-17
**Branch:** `release/1.0.0` (re-checked at `fcf511af755`, PR #10023)
**Status:** Plan. Status words follow the vocabulary below and come from fresh
source reads at the tip, not from the report's pinned snapshot `f9de7784163`.
No compiler, interpreter or SSpec run was performed for this document.
**Source:** consolidated robustness report (2026-11-17, §1–§19), owner-pasted.
The ten §1 items are **owner decisions**; everything else in that report is a
recommendation until selected here.
**Design:** `doc/05_design/language/robust_types/robustness_effects_arrow_pin_design_2026-11-17.md`
**Sibling plan:** `robust_boundaries_library_units_sffi_backends_plan_2026-11-15.md`
(units/boundary/SFFI — PRs #9941..#10002 landed; see its Implementation log).
This plan does not re-plan that work.

## 0. Owner decisions (from report §1, binding)

1. Ordinary compilation stays lightweight; medium/high analyses default on in
   lint and in explicitly selected diagnostic builds only.
2. Safety does not disappear when lint is off (no optional soundness).
3. Typestate already exists; extend it, do not add a second state system.
4. Finish the effect system under one contract for compiler, interpreter,
   loader, LSP, lint, imported/generated code.
5. Complete `must_use` enforcement on real typed call results.
6. Add/complete a real pinning (address-stability) contract.
7. Revive `x->method(args)` == `x = x.method(args)` (single evaluation,
   ownership/type rules). No unrelated record-update syntax.
8. Immutable object content and mutable bindings are compatible.
9. Keep `Immutable<T>`, `RevisionImmutable<T>`, `FrozenImmutable<T>` distinct.
10. Research is not adoption; non-selected features stay recommendations.

## 1. Status vocabulary

| Status | Meaning |
|---|---|
| Present | Implementation or executable spec located at the tip; completeness still qualified |
| Partial | Machinery exists; wiring, semantics, parity or coverage incomplete |
| Planned | Requirement/plan exists; implementation not demonstrated |
| Not demonstrated | Bounded read did not find it; not a claim that nothing exists |
| Proposed | New item introduced by the report/this plan |

## 2. Inventory re-checked at the tip (2026-11-17)

| Item | Status | Fresh evidence (file:line) | Delta vs report |
|---|---|---|---|
| `must_use` discard check | Partial | `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:157-191` — only `EXPR_CALL` whose callee is `EXPR_IDENT`; builds `error[R9]` text and pushes to `eval_warnings` (`eval.spl:307`), then still runs `eval_expr(eid)` (`:191`). No reader of `eval_warnings` under `src/compiler/80.driver` or `src/app`. `must_use` appears only in 5 interpreter files; nothing in `30.types`/`35.semantics`/HIR | Unchanged. Not enforcement |
| Bounded-loop classifier | Partial (unsound as documented) | `src/compiler/35.semantics/effect_validation.spl:109-128` — `effect_while_bound` returns `LOOP_BOUND_CONST` for any `Binary(_, _, IntLit)`; operator and induction progress unchecked. Docstring `:112-114` claims fail-closed. `effect_for_bound` `:130-150` returns `CAPACITY` for any non-range iterable | Unchanged. Overclaim stands |
| Effect inference unknown handling | Partial | `src/compiler/30.types/type_infer/inference_effects.spl:99-117` — unresolved callee pushes `EffectKind.Unknown` and clears `current_function_effects_complete`. `Await` has no arm and lands in `case _` (`test/01_unit/compiler/semantics/effect_inference_unknown_spec.spl:91-107`) | Unchanged |
| Safety severity map | Present | `src/compiler/80.driver/driver_safety_severity.spl:59-75` — robust -> Warn; critical/verified -> Deny; others Advisory | Unchanged |
| `->` in the Rust seed | Present | `src/compiler_rust/parser/src/expressions/postfix.rs:577-593` — `Expr::FunctionalUpdate`, match-guard depth guard `:580` | Unchanged |
| `->` in the self-hosted frontend | Not demonstrated | `src/compiler/10.frontend/core/parser_expr.spl:32` imports `TOK_ARROW` but has no postfix arrow branch; `parser_stmts.spl:2422-2450` consumes `->` only as the match-arm separator; no `FunctionalUpdate`/`functional_update` symbol anywhere in `src/compiler/**/*.spl` | Confirms the report's parity gap; now scoped precisely |
| `->` usage spec and requirement page | Partial (mislabelled) | `test/03_system/feature/usage/functional_update_spec.spl:60-158` — titles say struct/nested/"maintains immutability", bodies assert array/dict length and contents; `doc/02_requirements/language/functions/functional_update.md:7-12` says "immutable records and structs" | Unchanged |
| Fast/deep rule tiers | Not demonstrated | Lint has an evidence tier (`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:1177-1251`, `LintEvidenceTier`), not a cost tier or diagnostic profile; no `--diagnostic=` or `lint --fast` surface found | New reading; report §4 spellings remain proposals |
| Immutable views / revisions / async init | Partial, verification-pending | `doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md:152-169` — IMM-01/02 lane first; ASY-02 `E_ATTR_NOT_READY` landed; REV-01 lease 6/6 verification-pending; `E_INIT_CAPABILITY_ESCAPE` default off | Report §6 agrees; keep default-off milestones |
| Pin / self-reference | Not demonstrated | Only cache/package "pin" helpers (`80.driver/cache/pinned_archive_capability.spl`, `00.common/assurance/package_pins.spl`); no language-level address-stability contract | Unchanged |
| Typestate | Present (representation) | `doc/05_design/language/robust_types/robust_types_layer_contracts_2026-11-12.md` §1, §6, §7 | Unchanged |
| Units / boundary / SFFI | Present, Partial per slice | 2026-11-15 plan Implementation log (rows 2026-11-15..17); e.g. `bound_late_cast.spl` SPL-BOUND-001/002, `unit_value_binop` SPL-UNIT-002 | Landed since the report; superseded rows of report §2.1 |

## 3. P0 lanes (in order)

Each lane: TDD first (failing spec, then implementation), Fable brief + review,
land as verification-pending. No lane blocks on SMT, dependent types, an actor
runtime or a GC.

### P0-1 `must_use` enforcement (ROB-USE-01/02/03)
- Owner files: `10.frontend/core/interpreter/eval_stmts.spl` (`eval_stmt_expr`),
  `eval_tables.spl` (registry), a new typed-HIR discard check under
  `35.semantics/` (one authority; interpreter consumes it), `80.driver`
  severity projection (`driver_safety_severity.spl` or a sibling), TLDR/SMF
  metadata carrying the obligation.
- TDD spec: `test/01_unit/compiler/semantics/must_use_discard_spec.spl`
  (direct/method/imported/generic-return discard; return/assign/`?`/`match`/
  `val _ =` consumption; critical/robust severity → admission failure).
- Exit evidence: the three ROB-USE specs green; a critical-profile discard
  yields a non-zero admission result, not a string in `eval_warnings`;
  interpreter and native produce the same diagnostic identity.

### P0-2 Bounded-loop overclaim fix (ROB-EFF-04)
- Owner files: `35.semantics/effect_validation.spl:109-150`,
  `35.semantics/effect_verifier.spl` (`check_bounded_loops`).
- TDD spec: `test/01_unit/compiler/semantics/effect_loop_bound_soundness_spec.spl`
  (`while i < 10` with no induction progress → NONE; `while i != 10` → NONE;
  custom non-finite iterable → not CAPACITY; proven `i += k`, k>0, `<` literal → CONST).
- Exit evidence: no CONST/CAPACITY verdict from surface shape alone; docstring
  `:112-114` true again; `effect_verifier_spec` unchanged green.

### P0-3 Effect admission / unknown handling (ROB-EFF-01/02/03)
- Owner files: `30.types/type_infer/inference_effects.spl`,
  `30.types/type_system/effects.spl` (SCC), `10.frontend/effect_registry.spl`,
  loader/TLDR summary carrier, lint explain path.
- TDD spec: `test/01_unit/compiler/semantics/effect_admission_spec.spl`
  (callback/trait/imported unknown → Unknown, never pure; `Await` arm explicit;
  restricted region (`nogc`/pure/nonblocking) rejects unproven effect;
  changed dependency effect invalidates the cached summary).
- Exit evidence: one versioned effect summary (design §3) consumed by
  interpreter, native, loader, LSP; stale summary rejected in a test.

### P0-4 Arrow revival parity (ROB-ARR-01..07)
- Owner files: `10.frontend/core/parser_expr.spl` (postfix arrow, guarded as
  in `postfix.rs:580`), `10.frontend/ast.spl` + `_FlatAstBridge/convert_nodes.spl`
  (node), `desugar/` or HIR lowering to call + place-store, interpreter
  `eval_expr`, native MIR lowering; fix `functional_update_spec.spl` names.
- TDD spec: `test/01_unit/compiler/frontend/arrow_functional_update_spec.spl`
  (parse/lower) and `test/03_system/feature/usage/functional_update_spec.spl`
  (renamed scenarios + retained-original alias assertions, ROB-ARR-02).
- Exit evidence: same source accepted and lowered by seed, self-hosted
  interpreter and native; `val`/temporary/type-mismatch targets are named
  errors; indexed target evaluated once; `->f()?` orders propagate-before-store.

### P0-5 Fast/deep tier registry (ROB-COST-01/02)
- Owner files: `90.tools/lint/_LintMain/config_and_model.spl` (add cost tier
  beside `LintEvidenceTier`), lint rule registration, `80.driver` build
  profile (`--diagnostic=medium|high`, `lint --fast`), completeness status
  enum {pass, fail, incomplete, timed_out, unsupported, not_applicable}.
- TDD spec: `test/01_unit/compiler/lint/rule_cost_tier_registry_spec.spl`
  (normal build runs Low only; default lint runs all under budget; budget
  exhaustion → `incomplete`, never pass; robust CI fails on incomplete).
- Exit evidence: registry table lists every rule with a tier; a timed-out
  high rule is reported `timed_out`; warm-build wall/RSS recorded before and
  after with binary identity (`readlink -f bin/simple`), no numbers invented.

## 4. Phases (report §16) with test IDs (report §17)

| Phase | Work | Items | Test IDs | Status |
|---|---|---|---|---|
| P0-A correctness baseline | honest inventory (§2 above); result/severity admission; boundedness overclaim | P0-1, P0-2 | ROB-USE-01..03, ROB-EFF-04 | Planned |
| P0-B fast/deep split | rule registry, tiers, lint defaults, diagnostic profiles, completeness statuses | P0-5 | ROB-COST-01, ROB-COST-02, ROB-CACHE-01 | Not demonstrated → Planned |
| P0-C effects completion | canonical summaries; callbacks/imports/generated; loader validation; shared diagnostics | P0-3 | ROB-EFF-01..03, ROB-PARITY-01 | Partial → Planned |
| P0-D arrow revival | binding-update semantics; seed/self-hosted parity; place + error ordering | P0-4 | ROB-ARR-01..07 | Seed Present / self-hosted Not demonstrated |
| P1-A ownership/pinning | address-stable lifecycle, projections, field-copy, FFI/DMA boundaries | design §4 | ROB-PIN-01, ROB-PIN-02 | Not demonstrated → Proposed |
| P1-B init/concurrency | ready-state publication, capability escape, transfer/share, suspension | immview/revhooks lanes | ROB-INIT-01, ROB-STATE-01 | Partial (verification-pending) |
| P1-C library migration | Result/future/update APIs, units, SFFI adapters, immutable collections | 2026-11-15 plan | ROB-BOUND-01 | Present/Partial per slice |
| P2 advanced verification | resource/refinement/termination proofs, MIR diagnostics, reuse optimisation | — | (property/differential tests) | Proposed |

Test ID → scenario → expected result is report §17 verbatim; a spec title must
state what its assertions establish (see `functional_update_spec.spl` for the
counter-example).

## 5. Performance evidence rule

Before any default-on claim: unchanged warm build, one-function edit,
public-contract edit, dependency-effect edit, cold build; wall + CPU p50/p95,
peak RSS, cache hits/misses, rule-level overhead; always with binary identity.
No budget in this plan is numeric until measured.

## 6. Documentation reconciliation (report §18, done in this change)

- `doc/02_requirements/language/principles.md` — link + arrow/tier note.
- `doc/02_requirements/language/functions/functional_update.md` — claim
  corrected (binding update of array/dict vars, not record copy) + link.
- `doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md`
  — link; three contracts reaffirmed; arrow interaction.
- `doc/05_design/language/robust_types/robust_types_layer_contracts_2026-11-12.md`
  — link to the effects/arrow/pin design; no second typestate.
- 2026-11-15 plan Implementation log — one row.

## 7. Completion definition

A feature is complete only when parser/type/HIR/MIR/runtime requirements,
negative tests, imported/generated-code behaviour, native/interpreter parity,
diagnostic severity, documentation and the performance gate agree. A registry
entry, a bootstrap-only parse, or a generated `pass` row does not qualify.


## Implementation log

- 2026-11-18 P0-3 slice: `inference_effects.spl` — non-function callee type and
  trait-method calls now infer Unknown (incomplete row); `Await` has an explicit
  Async arm; `effect_region_admission` rejects Unknown in pure/nogc/nonblocking
  regions with `EFF-E0301`. Spec `effect_admission_spec.spl` 6/6 (was 1/6 red).
  Remaining: loader/versioned summary + stale-summary rejection, wiring the
  admission check into the driver region checks, imported-function summaries.
- 2026-11-18 P0-1 slice (verification-pending): `35.semantics/must_use_discard.spl`
  is the typed-HIR discard authority (SPL-USE-001 Result/Option discard,
  SPL-USE-002 `@must_use` name; `must_use_finding_severity` = error compiled /
  warning script). Spec `test/01_unit/compiler/semantics/must_use_discard_spec.spl`
  10/10 (was 0 executed, module missing). Existing specs unchanged:
  must_use_spec 4/5 (1 pre-existing failure), ignored_return_warning 4/4,
  must_use_streaming_scan 4/4.
  TODO (open): interpreter `eval_stmt_expr` still emits its own `error[R9]`
  strings and does not consume this check; method-call return types and
  imported callees are not resolved (only `@must_use` method names match);
  `80.driver` admission projection and TLDR/SMF obligation metadata not wired.
- 2026-11-18 P0-1 review fixes: only the exact `_ = f()` shape (unit Block, one
  Expr stmt, NilLit tail) is skipped; other blocks are scanned; with/try/lambda
  block bodies walked; callees resolve per module (no cross-module name match;
  unresolved calls are not flagged, TODO in source for import-table
  resolution); `MUST_USE_CODE_*`/`MustUseFinding` are `pub`; unused severity
  `code` param removed. Spec now 18/18. with/try/lambda walkers have no spec
  case yet (source syntax not confirmed).
- 2026-11-18 P0-5 slice 1: `90.tools/lint/_LintMain/rule_cost_tier.spl` adds LintCostTier (Low/Medium/High; unlisted = High), registry covering all `all_lint_names()`, LintCompleteness, `lint_rules_for_profile`, `lint_completeness_reduce` (exhausted budget -> incomplete). Spec `rule_cost_tier_registry_spec.spl` 6/6. Remaining: `lint --fast` / `--diagnostic` wiring, timed_out enforcement per rule, warm-build wall/RSS evidence.
- 2026-11-18 P0-4 (ROB-ARR-01/03/04 slice): self-hosted parser now parses postfix `x->m(args)` and desugars it to `x = x.m(args)` (`parser_expr.spl` `parse_arrow_update`); match patterns/guards parse with the arrow suppressed so arm and return-type arrows are unchanged; `val` and temporary targets are named parser errors. Spec `arrow_functional_update_spec.spl` 16/16 (block-scoped val tracking, nested-fn hide/restore, `val (a, b)`); `functional_update_spec.spl` titles corrected; non-simple field/index bases are a named error until ROB-ARR-05 single-evaluation. Open: module-level `val` not parser-checked, `->f()?` ordering, type-mismatch error, `a->b()->c()` chains, native MIR parity evidence.
- 2026-11-18 P0-4 (ROB-ARR-05/06): `x->m()` places with non-simple base/index (`a[f()]`, `g().x`) now desugar to a block binding fresh `val __arrow_<off>_<n>` temps first, so each is evaluated once (named error dropped for index operands; a non-lvalue root such as `g().x` or `g()[i]` and a bare call target stay a named error); `x->f()?` desugars to `x = (x.f())?` so propagation precedes the store. `arrow_functional_update_spec` 21/21; functional_update 11/11; match_arrow_arm_parse 16/16, match_pipe_arrow_arm_parse 5/5, match_case_fat_arrow 9/9, optional_member_call_parser 5/5. Runtime-counter proof is structural (AST call count), not executed.
- 2026-11-18 drvwire (ROB-EFF-03, ROB-USE-01/02 wiring): `collect_module_typecheck_receipt_v1` (hir_typecheck_consumer_v1.spl) now runs `must_use_discard_scan` (error compiled / warning when `script_mode`, bounded by pass severity: Advisory drops, Warn downgrades; default profile is Advisory so existing repo code is not newly failing) and `infer_function` calls `check_effect_region` -> `effect_region_admission` (EFF-E0301) for functions with an `@pure`/`@nogc`/`@nonblocking` attribute (new trailing `HirFunction.effect_region`, set in declaration_lowering). Spec `test/01_unit/compiler/driver/robust_checks_wired_spec.spl` 5/5 (was 2/5 before wiring); effect_admission 9/9, must_use_discard 18/18, compiler_core/must_use 4/5 unchanged. Remaining: `@must_use` name set is passed empty (HirFunction carries no attributes); cross-module callees and method return types still unresolved; EFF-E0301 treats any non-local callee as Unknown (by design of ROB-EFF-01).
- 2026-11-18 P0-5 slice 2: `simple lint --fast` wired (`lint_entry.spl` -> `cli_lint_commands`; `LintCliPolicy.fast`; `lint_apply_fast_profile` silences every non-Low rule via config level Allow) and a `lint completeness: pass|fail|incomplete|timed_out` status line (also `completeness` in `--json` summary) via `lint_completeness_reduce`. Spec `lint_fast_profile_spec.spl` 4/4; `rule_cost_tier_registry_spec` 7/7, `collection_index_mutation_spec` 6/6 unchanged. CLI-verified: COLL019 shown by default, absent with `--fast`. Open: fast mode filters output but does not yet skip executing non-Low rules (no wall-time saving claimed); `--diagnostic=medium|high` and per-rule timed_out enforcement not done; warm-build wall/RSS evidence still missing.
- 2026-11-19 rbfin item 3 (units, native `where`-only): `unit_where_bounds` (`unit_constraint.spl`) derives inclusive integer min/max from `and`-joined `self`-vs-literal comparison chains (`1 <= self <= 65535`, `self >= 0`, strict `>`/`<` adjusted); the parser registers them as the unit's min/max text so the existing MIR SPL-UNIT-005 compare-and-panic covers `where` units. Shapes with `or`/`not`/parens/arithmetic/floats stay interpreter-only (no native bounds). Spec `unit_constraint_decl_spec` 20/20 (4 new red first). New native MIR cases in `unit_range_cast_native_spec` are tag only-compiled and, like the pre-existing 3 range cases, fail under the Rust seed (cast lowers to a Struct, no check emitted) — need a pure-Simple/native run to verify.
- 2026-11-19 rbfin item 2 (`@must_use`): `FunctionAttr.is_must_use` (trailing defaulted field, set by `parse_function_attrs`) carries the attribute into HIR; `must_use_discard_scan` now adds attribute-marked functions to the per-module marked set and resolves imported callees through `HirModule.imports` (alias-aware, against the scanned module set; unknown module/item not flagged). Spec `must_use_discard_spec` 24/24 (cross-module cases built by turning a local stub into an import, since HIR lowering has no in-memory module loader); must_use_streaming_scan 4/4, ignored_return_warning 4/4. Open: the driver (`hir_typecheck_consumer_v1`) still scans a single module so cross-module findings need the project HIR set passed there; interpreter `eval_stmt_expr` still uses its own R9 path.
- 2026-11-19 rbfin item 4 (closure unit scope, Rust seed): a unit-suffix literal inside a closure body took its scope owner from `CURRENT_EXEC_MODULE` (the invoking frame), so a lambda written in module A and called from B used B's scope. `units::scope::literal_scope_owner()` now uses `private_call_caller()` (closure origin stamp = writing module, else executing owner) in `interpreter/expr/literals.rs`. Rust unit test `closure_literal_resolves_in_writing_module_scope` + 2 existing module_scope_tests: 3/3 (`cargo test -p simple-compiler --lib module_scope_tests`, CC=clang-cl). NEEDS A SEED REDEPLOY to take effect in `bin/simple`; no .spl spec added (the bundled seed binary predates the fix).
- 2026-11-19 rbfin item 1 (`lint --fast`): re-checked at release/1.0.0 tip; no code change needed. `--fast` already applies `lint_apply_fast_profile` (non-Low rules set to Allow before any producer runs; `lint_fast_profile_spec` 4/4 asserts zero `collection_performance` invocations) and the run budget is live (`--budget-ms`/`--max-files`/`SIMPLE_LINT_BUDGET_MS`, `LintRunBudgetV1`, child stats carry `budget_exhausted`; `budget_exhausted: false` remains only in the legacy `simple_lint_adapter_result` default constructor).
- 2026-11-19 rbpost (post-merge review fixes for PR #10182 and #10358): (A) `emit_unit_div_remainder_check` now branches on `divisor == 0` BEFORE the `Rem` (skip to the join block; no hardware trap), `unit_div_payload_word` loads field 0 of a record-shaped unit wrapper (it is a pointer to a headerless field block, so the old bitcast read the address) and only bit-casts non-record words, and `emit_unit_range_check_by_name_v1` types the bound constants with the raw value's own MIR type so U64 operands compare unsigned. (B) `TODO(ROB-USE-01)` restored in `must_use_discard.spl` (driver still passes one module; cross-module must_use stays dormant); `unit_where_bounds` rejects i64-overflowing literals and `n+1` at i64 max (bound dropped), and `unit_where_bounds_empty`/`unit_bound_texts_empty` make the parser reject empty `where` and `in` ranges. Specs: unit_constraint_decl 25/25 (4 new red then green), must_use_discard 24/24, unit_div_remainder_native 5/5 (2 new red/green under the seed). unit_range_cast_native 2/9 under the seed: the 6 range-check cases fail PRE-EXISTING (identical before this change) and the new u64 case fails for the same seed-native reason; needs a native run. Still open from the #10182 review: panic message uses `<runtime value>`, non-name `Port(raw)` operands unchecked, `must_use_find_module` suffix ambiguity, CStr facade textual dispatch.
- 2026-11-22 robunit (follow-up to the #10182 review "Still open"): (a) the native range-check panic now embeds the offending value (`SPL-UNIT-005: value <n> violates the constraint of unit ...`), built at runtime from `rt_raw_i64_to_string` + `rt_strcat_tagged` in the fail block (`emit_unit_range_panic_if`), replacing the `<runtime value ...>` placeholder; (b) non-name `Port(expr)` operands were already checked once after construction (rbfu2, `lower_struct_construct` wrapper) and now also assert the value render. Specs: `unit_range_cast_native_spec` 14/14 and `unit_constraint_decl_spec` 25/25 under the seed binary (2 new cases; written alongside the change, not observed red first). Still open: `must_use_find_module` suffix ambiguity, CStr facade textual dispatch; runtime panic text not yet observed in an executed native binary.
- 2026-11-19 provfix (PR #10351 review fix): the executor no longer calls `emit_provider_sidecar`; new `target_provider_admission` only READS the provider-owned `<artifact>.provider.sdn` via `provider_gate`. `emit_provider_sidecar` stays a provider-side helper and now refuses to overwrite an existing sidecar. Negative specs `target_executor_provider_sidecar_spec` 5/5 (missing -> provider-missing, wrong triple, wrong ABI, valid sidecar untouched, no emit call in executor); provider_entry 5/5, provider_gate 10/10, vector_length 5/5, backend_contracts 9/9. SVE VL documented as "kernel default VL, unverified on hardware".
- 2026-11-19 rbfu2 (post-merge review follow-ups for #10182, #10168, #10181): #10182 (a) range-check panic text now names the unit bounds (`<runtime value outside lo..hi>`); (b) `Port(expr)` for a non-name operand is checked after construction on the stored payload word, so the operand is evaluated once (`lower_struct_construct` wrapper over `lower_struct_construct_core`); (c) `must_use_find_module` is deterministic: exact key/name match first, else longest segment-boundary suffix, ties by smallest key. #10168: summary tail is now the real tail expression (base-indent, non-header, non-assignment line) plus any `return` at any depth. #10181: backend contract checks read parsed fields (`group`/`target` block keys, `PTX_ISA_VERSION` constant, parsed `cpu_tiers.sdn` arch tiers, `default:` key) instead of `contains()` on file text; `boundary_contract_digest` is documented as SELF-DERIVED from the receipt's own inputs and is not boundary-contract evidence. Verdicts: `must_use_discard_spec` 27/27, `bound_unit_reassert_summary_spec` 14/14, `bound_unit_reassert_spec` 11/11, `backend_contracts_spec` 12/12, provider receipt/identity/gate specs 11/11, 4/4, 10/10. `unit_range_cast_native_spec` is tagged only-compiled and its 10 range-check cases (existing and new) fail identically under the interpreted `bin/simple.exe` (its MIR carries no SPL-UNIT-005 check at all, baseline included), so (a)/(b) are UNVERIFIED until a compiled-lane run.
- 2026-11-19 rbnative (native verification of unit range-cast/remainder checks): `unit_range_cast_native_spec` passed 2 of 9 under the Rust seed (also with `--mode native`, which falls back to the interpreter: seed has no MC/DC/native probe emission, and no self-hosted native compiler is deployed here). Root cause is a REAL bug, not a seed limit: `parse_and_build_module_with_scope_owner` ends with `unit_scope_restore(saved_unit_scope)`, which restores the pre-parse unit decl pool AND the constraint pool (`unit_constraint_*`), so the file's own `unit Port: i32 in 1..=65535` constraint row is discarded before MIR lowering. `emit_unit_range_check_by_name_v1` then sees `unit_constraint_find(name) < 0` and silently emits no SPL-UNIT-005 check (probe: after `parse_full_frontend`, `unit_constraint_find("Port") == -1`). The driver goes through the same `parse_full_frontend`, so the compiled path was affected too. Fix: new `unit_constraint_pool_merge` + `unit_scope_restore_keeping_constraints` (restore the caller's scope, then re-register the just-parsed constraint rows); the bridge's end-of-parse restore uses it. Result under the seed interpreter: `unit_range_cast_native_spec` 9/9 (was 2/9; the u64 case "types the bound constants as u64" now passes, i32 stays signed), and `unit_constraint_decl_spec` 25/25, `unit_constraint_pool_lifecycle_spec` 2/2, `unit_scope_bridge_isolation_spec`, `unit_scope_cache_lifetime_spec`, `compiled_unit_suffix_scope_spec` 10/10, `newunit_pool_reset_spec` all green. Status: verification-pending for real native execution (MIR-level assertions verified; no native-built compiler available on this host to execute the emitted `rt_panic` path or the unsigned u64 compare in machine code).
- 2026-11-19 rbfu1 (post-merge review follow-ups #10345, #10346): (A) `EnumReturn` gains an explicit `abi_type` (no more implicit i32); non-integer/empty widths are rejected with SPL-SFFI-RANGE-001, and a width that differs from the compiled C enum fails a compile-time `_Static_assert` in the spec harness. `sffi_cabi_fixture_spec.spl` now links a C harness (facade raw ABI type) against `cabi_fixture.c` (new `fx_bool_bad`/`fx_enum_oob`, `main` guarded by `SFFI_FIXTURE_NO_MAIN`), uses `process_run("clang", ...)` + `mkdir_p`/`file_write` only (no POSIX shell, Windows-safe, clang only). 10/10 pass on Windows. (B) `bound_origin_facts.spl`: multi-line fn signatures are joined by paren depth (params on continuation lines recorded at the signature line, top-level comma split), and `val (a, b) = ...` tuple bindings emit one fact per name (`_` skipped). `bound_origin_facts_spec.spl` 7/7 pass (2 new scenarios failed before the fix).
- 2026-11-19 rbnat2 (native execution attempt of unit range-cast/remainder checks): five fixtures in `test/fixtures/unit_native/`. Rust-seed native-build (`SIMPLE_NATIVE_BUILD_RUST=1`, llvm-mingw; clang-cl fails to link) builds and runs them, but the seed emits no unit checks: port_oor exit 0 (`UNREACHED` printed), big_reject exit 0 (`UNREACHED`), port_in/big_accept exit 0, div_zero exit 132 SIGILL (hardware trap). The pure-Simple native-build via the seed interpreter timed out at 900 s (rc=124). Native verification of the pure-Simple checks remains BLOCKED; see `doc/08_tracking/bug/unit_range_cast_native_execution_blocked_2026-11-19.md`.
- 2026-11-19 rbfu3 (follow-ups to rbfu1 and #10468): (A) `bound_origin_facts.spl`: the top-level comma splitter and paren-depth scan now skip string literals (`sep: text = "a, b), c"` is one param), and nested tuple patterns `val ((a, b), c) = ...` bind a, b and c (matching-paren scan plus recursive pattern walk). 2 new scenarios red then green; `bound_origin_facts_spec` 9/9. (B) New `unit_constraint_visibility_spec` (4/4) pins that `unit_scope_restore_keeping_constraints` makes only the parsed file's declared rows visible on top of the caller's (no leak, no rows when the file declares none). Same-name unit with DIFFERENT bounds: policy chosen = deterministic, the parsed file's row wins on merge (MIR lowering of that file must see its own bounds); no clash diagnostic is emitted (a detector with no caller was dropped as unused code; add one together with its diagnostic if wanted). No bug found in the existing merge. Verdicts: `unit_scope_bridge_isolation` 2/2, `unit_scope_cache_lifetime` 2/2, `unit_range_cast_native` 12/12 (interpreted).
- 2026-11-22 bd1 (robust boundary lint completion): (1) SPL-BOUND-002 autofix variants in `90.tools/fix/rules/impl_/bound_late_cast_fix.spl`, registered in `rules/registry.spl` as `SPL-BOUND-002-CONSTRAINED` (range-checked adapter `<adapter>_checked` returning `Unit?` for units declared `in LO..=HI`; direct-call sites only; the rewritten site now yields an Option the reviewer must handle), `SPL-BOUND-002-MOVE` (only the `val r = ext(args)` + late cast sites of the adapter fix) and `SPL-BOUND-002-ALLOW` (inserts `@allow(bound_late_cast) # reason: <text>` above the offending fn; a blank reason yields no candidate, the registry form takes the reason from a `# reason:` comment the author wrote directly above the header). The lint (`bound_late_cast.spl` `_blc_exempt`) honours the annotation only with a non-empty reason, function-scoped, SPL-BOUND-002 only (SPL-BOUND-001 still reports). `std.common.diagnostics.fix_transaction` supports multi-file candidates, but all three variants are single-file (no cross-file adapter rewrite); all are Uncertain/review-required. The MOVE and base candidates overlap on move sites, so a full `run_registry_producers` proposes both; neither is auto-applied. (2) Cross-file summaries: new `80.driver/driver_bound_summaries_v1.spl` (`driver_bound_import_graph_v1`, `driver_bound_summaries_v1`, `driver_bound_findings_v1`) builds the import graph from the driver's module inventory (module id -> source) with one project-wide memo and feeds `check_bound_late_casts_cross`; cycles terminate, unresolved imports give no summary. Not yet called from the compile pipeline (`hir_typecheck_consumer_v1` still single-module) and the lint rule still uses its own on-disk resolver; the memo is order-sensitive inside import cycles (no raw fn is reported through a cycle either way). Specs (red first, then green): `bound_late_cast_variants_spec` 6/6, `bound_late_cast_allow_spec` 2/2, `driver_bound_summaries_spec` 4/4, `bound_late_cast_registry_spec` 5/5 (2 new); unchanged `bound_late_cast_fix_spec` 11/11, `bound_late_cast_spec` 55/55, `bound_cross_file_spec` 5/5, `bound_import_graph_spec` 7/7 (interpreted `bin/simple.exe`, Rust seed, no MC/DC evidence).
