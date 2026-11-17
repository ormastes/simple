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
