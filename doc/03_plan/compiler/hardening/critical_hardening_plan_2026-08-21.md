# Critical Hardening Plan — phases 0–9, waves 0–5

**Date:** 2026-08-21
**Research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` (§15, §20, §21, §24)
**Design:** `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md`
**Status legend:** `not started` / `partial` (with evidence) / `done`

Every phase exit gate below is an **executable verdict line** in the repo convention
(`PASS — <n> ... checked, ...` exit 0 / `FAIL — ...` exit 1 / `ERROR — nothing was checked` exit 2;
a run that checked 0 items is ERROR, never a pass). No phase may be marked done from prose.

---

## 0. What already exists today

| Asset | Where | Note |
|---|---|---|
| Critical assurance profile + REQ-MC ids | `doc/02_requirements/language/mission_critical_profile.md` | REQ-MC-001..014, 023 allocated; **015–022 explicitly reserved-but-unallocated** (`:233`) |
| Typed policy resolution + SDN project pinning | REQ-MC-013 / REQ-MC-014 (both marked IMPLEMENTED 2026-08-07) | |
| Id-keyed match coverage | `src/compiler/20.hir/match_coverage.spl` | but `is_exhaustive():36` returns true on a wildcard |
| Safety + typecheck HIR passes | `src/compiler/80.driver/driver_hir_pipeline_passes.spl:82,146` | both **fail-open warn** passes by their own comment (`:98`) |
| Typed mono table + real specialization + real module rewrite | `40.mono/monomorphize/table.spl:29,39`, `monomorphize_integration.spl:433,457,527` | landed after the research snapshot |
| Recursive type substitution | `40.mono/monomorphize/type_subst.spl:74-128` | still wildcard-closed at `:127` |
| Aspect pack catalog/container/routed load | `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`, `doc/09_report/aspect_pack_design_coverage_2026-08-18.md` | |
| Pre-push guard convention + 9 live guards | `scripts/check/check-*.shs`, `.claude/rules/vcs.md` | the verdict-line/selftest/non-vacuity pattern all new gates must copy |
| Coverage-guard precedents | `scripts/check/check-coverage-not-silent-noop.shs`, `check-backend-evidence-branch-coverage.shs` | **no** completeness/exhaustiveness/Any/mono guard exists yet |
| Parallel-agent ownership discipline | `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md` | reuse verbatim |

New requirement ids proposed by this plan (see §Wire-up): `REQ-MC-ANY-001`, `REQ-MC-MONO-001`,
`REQ-MC-COMPLETE-001`, `REQ-MC-PIPE-001`, `REQ-MC-ASPECT-001`, `REQ-MC-BOOT-001`. Verified free:
`grep -rn 'REQ-MC-(ANY|MONO|COMPLETE|PIPE|ASPECT|BOOT)' doc/` matches only the research doc §14.
The numeric block 015–022 is left reserved and untouched.

---

## Phases

### Phase 0 — Contract lock and truth inventory — `partial` (lock landed 2026-08-21; gate honestly RED on registry freshness)
- **Deliverables:** canonical schema-registry format; `CoverageState`; static/complete/dyn semantics;
  stable extension identity; `type_erasure` capability; `MonoSemanticKey`/`MonoArtifactKey`; aspect
  seal schema; diagnostic id ranges; package migration inventory. Machine-readable census of: `Any`
  decls/fields/returns/params, compiler wildcard matches, `NilLit`/`Error`/`pass`/`0` fallbacks,
  unhandled enum variants, generic defs/calls, unsafe ops, aspect/dyn registration points, duplicate
  semantic tables, engine-specific fixtures.
- **Owning paths:** `doc/02_requirements/language/critical_completeness.md`,
  `doc/04_architecture/compiler/extension_completeness.md`, `src/compiler/00.common/completeness/**`,
  `src/compiler/00.common/dynamic_identity/**`, `spec/compiler_schema/**`.
- **Exit gate:** `sh scripts/check/check-completeness-contract-lock.shs` →
  `PASS — <n> contract artifact(s) checked, census regenerates byte-identically`. No behavior change.
- **Status 2026-08-21:** contract docs, `scripts/check/check-completeness-contract-lock.shs`
  (fatal `--selftest`, `--update-lock`, `--no-census`), `spec/compiler_schema/contract_lock.sdn`
  (32 artifacts hashed) and `test/01_unit/scripts/completeness_contract_lock_gate_test.shs` landed.
  Evidence: `--no-census` -> `PASS — 32 contract artifact(s) checked, hash locked`; a one-line doc
  edit -> `FAIL — ... contract hash drifted` exit 1. Full gate is RED, not by this lane: delegated
  `check-compiler-schema-fresh.shs` reports `FAIL — stale: compiler.frontend.PatternKind.sdn
  compiler.hir.HirPatternKind.sdn index.sdn` (uncommitted registry edits from a parallel session).
  Remaining for `done`: registry regenerated + full gate green; `UNLANDED` rows (E-MC-DYN codes,
  per-enum diagnostic ranges, aspect seal file schema) stay contract-only until their phases.

### Phase 1 — Make missing paths loud everywhere — `partial` (C2, C5 landed 2026-08-21)
- **Deliverables:** replace silent FlatAst/AST/HIR/MIR fallbacks with explicit diagnostics; total
  transition tables; generated exhaustive visitors; fatal critical-wildcard rule; explicit MIR
  decision for **all 26 `HirTypeKind` variants**; named errors with spans; `simple compiler coverage`.
- **Owning paths:** `10.frontend/_FlatAstBridge/**`, new `20.hir/generated/**`,
  `50.mir/mir_lowering_types.spl`, `50.mir/_MirLowering/function_lowering.spl`,
  `50.mir/_MirLoweringExpr/expr_dispatch.spl`, `95.interp`, new `00.common/transition/**`,
  `90.tools/` + `src/app/cli/dispatch/table.spl`.
- **Exit gate:** `sh scripts/check/check-compiler-transition-coverage.shs` →
  `PASS — <n> transition row(s) checked, missing=0 silent-fallback=0 critical-wildcard=0`.
- **Blocking bug:** `doc/08_tracking/bug/mir_lowering_missing_hirtypekind_arms_wildcard_fatal_2026-08-05.md`.

### Phase 2 — `Any` boundary and representation stabilization — `partial` (Y1/Y2 census + checker landed 2026-08-21)
- **Deliverables:** `type_erasure` unsafe capability; HIR `AnyEscapeChecker`; fix remaining Any
  storage/consumer parity bugs *before* unsafe-Any is a supported boundary; one canonical
  RuntimeValue box/unbox/compare/render API; generated type-directed conversion replacing duplicated
  boxing; compiler registries `Any` → typed records; `WireValue`/result enums; ban new core `Any`.
- **Owning paths:** new `35.semantics/any_escape/**`, `00.common/assurance/**`, one canonical runtime
  value module, Rust-seed counterpart.
- **Severity ramp:** moderate=inventory, strict=warn + public-API deny, robust=deny core+boundaries,
  critical=deny outside unsafe + deny escape.
- **Exit gate:** `sh scripts/check/check-any-escape.shs` →
  `PASS — <n> Any site(s) checked, outside-unsafe=0 escaping=0` (ratchet baseline first, like
  `check-unbacked-extern-ratchet.shs`).
- **Prior evidence:** `doc/08_tracking/bug/any_slot_holds_untagged_scalar_2026-08-05.md`,
  `.spipe/any-any-native-divergence/state.md`.

### Phase 3 — Typed monomorphization — `partial`
- **Already done (post-research-snapshot):** typed table (`table.spl:29,39`); real specialization
  (`monomorphize_integration.spl:433-451`); real module/call-site rewrite (`:457,:527`); recursive
  type substitution (`type_subst.spl:74-128`).
- **Remaining:** `SpecializationKey` → `MonoSemanticKey` (const/effect/capability args); HIR
  expr/stmt substitution module; root+use collector with a deterministic fixed point; post-mono
  verifier; exhaustive substitution (delete `type_subst.spl:127`'s `case _: ty`); keep the existing
  loud generic-native gates until every positive/negative fixture passes.
- **Owning paths:** `40.mono/monomorphize/{table,type_subst,rewriter}.spl`, new
  `40.mono/monomorphize/hir_subst/**`, new `40.mono/monomorphize/collector/**`, new `40.mono/verify/**`.
  `driver_hir_pipeline_passes.spl:53` (`monomorphize_impl`) is integrator-only.
- **Support order:** free fn 1 inferred arg → multi/explicit args → generic structs → generic classes
  → generic methods → generic enums (without breaking Option/Result) → trait bounds + associated
  projections → const generics/layout params → closures/drop glue/witnesses.
- **Exit gate:** `sh scripts/check/check-post-mono-invariants.shs` →
  `PASS — <n> module(s) checked, unresolved-typeparam=0 generic-call=0 any-erasure=0 error-type=0`.
- **Integrator status (2026-08-21):** `monomorphize_impl` now calls
  `run_monomorphization_with_diagnostics`, routes every E-MONO-030/E-MONO-032 finding to
  `ctx.add_error`, and returns `false` under a named `E-MONO-033` message rather than lowering
  non-monomorphic HIR to MIR. `post_mono_verify_modules` still runs before MIR and its enforcement
  threshold was RAISED from `critical`-only to `robust`+ (`strictness.at_least(Robust)`); no gate was
  relaxed. Both passes now record a `PassReceipt`. Exit gate green:
  `check-post-mono-invariants.shs` → `PASS — 10 fixture(s) checked, 0 unexpected`.
  Regression spec: `test/01_unit/compiler/driver/mono_pipeline_surfaces_unresolved_generic_spec.spl`.
  **Caveat:** `bin/simple` is still the Rust seed, which does NOT execute this pure-Simple driver
  path, so end-to-end `simple run` results do not exercise the wiring — only the pure-Simple specs do.
- **See also:** `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`.

### Phase 4 — Sum types and closed-match enforcement — `partial` (S2/S3 landed 2026-08-21)
- **Deliverables:** `@closed` and `@evolving(repr:, unknown:)`; enum payload metadata preserved end
  to end; canonical union lowering (`i64|f64|bool|text` → checked sum, never `Any`); invalid
  discriminant rejection; critical no-wildcard enforcement; compiler `Any` result families → closed
  enums; generated match-coverage witnesses.
- **Owning paths:** parser enum payload modules, new enum-contract checker, type-system union
  modules, `20.hir/match_coverage.spl` (`is_exhaustive():36` must stop honouring `has_wildcard`).
- **Exit gate:** `sh scripts/check/check-closed-match-coverage.shs` →
  `PASS — <n> match(es) checked, non-exhaustive=0 wildcard-closed-critical=0`.
- **Existing requirement:** REQ-MC-003 (enum contracts) already blocks on payload metadata.

### Phase 5 — Complete/dyn extension infrastructure — `partial` (D2/D3/D4/D5 landed 2026-08-21)
- **Deliverables:** `complete:` / `dyn:` grammar; extension manifests; required-interface
  verification; dense local id freeze; per-config seals; cache keyed by seal hash; persistent ids in
  serialized HIR/SMF; open `dyn` prohibited in critical.
- **Owning paths:** parser extension hooks, new extension-manifest modules, new
  `99.loader/completeness_seal/**`, `00.common/dynamic_identity/**`.
- **Exit gate:** `sh scripts/check/check-completeness-seal.shs` →
  `PASS — <n> selected constructor(s) checked, missing-capabilities=0 id-collisions=0 dyn-in-critical=0`.

### Phase 6 — Aspect compiler integration — `partial` (§13.7 steps 1-2 + exit gate landed 2026-08-21)
- **Deliverables (in the research doc's §13.7 order):** typed facet grammar/HIR → binding
  completeness/uniqueness → witness/sidecar ABI → core public ABI comparison → signature/trust
  verification → atomic generation publication → weave-plan production → post-weave critical
  verification. Weave typed HIR **before** final mono; re-run type/effect/safety after weaving.
  Hot unload stays out of critical scope.
- **Owning paths:** AOP planner/weaver modules, facet parser/HIR modules, existing aspect-pack
  adapter only (do not replace the catalog/container slice).
- **Exit gate:** `sh scripts/check/check-aspect-seal.shs` →
  `PASS — <n> aspect(s) checked, unbound-required=0 late-activation=0 post-weave-recheck=ran`.
- **Caution:** no signature-enforcement claim until a real verifier + authority are wired.
- **Status 2026-08-21:** §13.7 steps 1-2 landed as
  `src/compiler/35.semantics/aspect_seal/{facet_model,seal}.spl` (typed
  facet/advice/pointcut model, `binding_completeness`, `AspectSeal` with a sorted
  deterministic hash, closed `AspectSealReason` enum: `UnboundRequired`,
  `DuplicateBinding`, `LateActivationInCritical`, `UnverifiedSignature`,
  `OpenDynAdviceInCritical`, `EmptyPointcut`, `BadAxisValue` — no wildcard arms),
  plus `src/app/check/aspect_seal_census.spl` and the exit gate
  `scripts/check/check-aspect-seal.shs` (fatal `--selftest`, 5 fixtures under
  `test/fixtures/aspect_seal/`, ERROR exit 2 on 0 aspects or 0 obligations).
  Evidence: `--selftest` -> `PASS — 5 selftest fixture(s) checked, scanner detects
  all four rejection classes`; default scan -> `PASS — 1 aspect(s) checked,
  unbound-required=0 late-activation=0 post-weave-recheck=ran`; negatives ->
  `FAIL — 1 aspect(s) checked, unbound-required=1 ...` (exit 1) and
  `... unverified-signature=1 ...` (exit 1). 19 specs green
  (`test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl`, mirrored to
  `test/unit/`).
  **Scope: fixtures; weaver/witness ABI unlanded.** §13.7 steps 3-8 (witness/sidecar
  ABI, core public ABI comparison, signature/trust verification, atomic generation
  publication, weave-plan production, post-weave critical verification) are NOT
  implemented. `post-weave-recheck=ran` in the verdict means a STUB pass re-ran
  `binding_completeness` over the sealed set and re-derived the seal hash — no woven
  HIR is re-verified, because no weaver is wired. `UnverifiedSignature` is a REFUSAL
  of aspects that demand provenance, not a verification result: there is no verifier
  and no trust authority in this tree, and nothing here may be described as signature
  enforcement. Existing AOP/aspect-pack modules, parser, HIR, mono, MIR and the
  runtime were not touched.

### Phase 7 — Seed/self-host parity and bootstrap closure — `not started`
- **Deliverables:** identical generated schema/coverage tables from the Rust seed and the self-hosted
  compiler; `simple compiler parity --seed <bin> --self <bin>` comparing parser productions, enum
  variants/discriminants, transition states, diagnostics, accepted/rejected fixtures, HIR/MIR
  snapshots, unsafe+Any policy, complete/aspect manifest interpretation; Stage N builds Stage N+1
  under the same critical seal; two consecutive self-host stages produce equivalent manifests.
- **Exit gate:** `sh scripts/check/check-seed-selfhost-parity.shs` →
  `PASS — <n> manifest row(s) compared, diff=0`.
- **Blocked by:** all four tracked stage binaries currently SEGV — see
  `.claude/rules/vcs.md` (`check-stage-binaries-runnable.shs`, advisory/RED) and
  `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.

### Phase 8 — Critical islands → whole compiler — `not started`
- Package pin order: `00.common` → `10.frontend` → `20.hir` → `30.types`/`35.semantics` → `40.mono`
  → `50.mir` → `55.borrow` → `70.backend` → `80.driver` → `90.tools` → `95.interp` → `99.loader` →
  runtime/stdlib → SimpleOS/firmware.
- A package gets its `simple.sdn` critical pin only when: no waiver lacks owner+expiry; its
  dependency closure is ≥ robust; every critical check actually executes (not advisory); differential
  tests cover its semantics.
- **Exit gate:** `sh scripts/check/check-critical-package-pins.shs` →
  `PASS — <n> pinned package(s) checked, advisory-in-critical=0 waiver-without-expiry=0`.

### Phase 9 — Release evidence and default escalation — `not started`
- Critical release requires all of: static coverage 100%, selected-complete coverage 100%, missing
  transitions 0, `Any` outside unsafe 0, `Any` escape 0, unresolved generic in MIR 0, silent fallback
  0, reachable unsupported 0, seed/self-host parity diff 0, interpreter/JIT/native diff 0, unverified
  aspect 0, late dyn semantic module 0, stale evidence 0.
- **Exit gate:** `sh scripts/check/check-critical-release-seal.shs` →
  `PASS — <n> evidence receipt(s) checked, all fresh and bound to artifact+seal hash`.
- Only then consider escalating compiler/loader defaults from robust-at-warning to robust-deny or
  critical for selected release lanes.

---

## Waves (parallel-agent execution)

Coordination rule (unchanged from `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`):
shared contracts first, then disjoint file ownership; a single integration owner edits shared
dispatchers, root exports, profile tables, and aggregate gates. Each agent carries an `agent_scope`
SDN block (`id/allow/deny/inputs/outputs/red_tests/exit_gate`) and CI rejects out-of-scope edits.

| Wave | Content | Status |
|---|---|---|
| **0** serial contract lock | Architect A0 + reviewer R0 freeze closure schema, linkage/activation axes, extension identity, `CoverageState`, required operation interfaces, Any capability + escape rules, mono keys, aspect seal/lifecycle, diagnostics, registry format, evidence receipt format. No feature agent starts until both reviewers sign the contract hash. | `not started` |
| **1** independent foundations | A1 schema generator, A2 exhaustiveness, A3 transition model, A4 dynamic identity, A5 unsafe capability, A6 test harness, A7 perf baseline. Shared driver/parser files denied. | `partial` — A1–A6 landed 2026-08-21 (see Lane status below); A7 perf baseline `not started` |
| **2A** compiler path completeness | C1 grammar registry, C2 FlatAst bridge, C3 AST visitors, C4 HIR visitors, C5 HIR→MIR types, C6 HIR→MIR expr/stmt, C7 backend coverage, C8 interpreter coverage. Generated fragments merged by I0. | `partial` — C2, C5 landed 2026-08-21 |
| **2B** Any hardening | Y1 inventory, Y2 HIR checker, Y3 RuntimeValue ABI (**locks before Y4/Y5**), Y4 seed parity, Y5 self-hosted boxing parity, Y6 migration wrappers, Y7 boundary tests. | `partial` — Y1/Y2 landed 2026-08-21 (`35.semantics/any_escape/**`, `check-any-escape-census.shs`) |
| **2C** typed monomorphization | M1 types/table, M2 type substitution, M3 HIR substitution, M4 collector, M5 rewriter, M6 layout/type instances, M7 post-mono verifier, M8 seed parity, M9 code-size/cache. Integrator alone touches `driver_hir_pipeline_passes.spl` and relaxes gates after M1–M7. | `partial` — M1 (`table.spl:29,39`), M2 (`type_subst.spl:74-128`) and most of M5 (`monomorphize_integration.spl:457,527`) already landed |
| **2D** sum types / enum contracts | S1 payload preservation, S2 `@closed`, S3 `@evolving`, S4 union normalization, S5 layout/serialization, S6 Any→sum migration. | `partial` — S2/S3 landed 2026-08-21 (generated attributes on `HirEnum` + `35.semantics/enum_contract/**`) |
| **2E** complete/dyn + aspects | D1 extension grammar, D2 manifest generator, D3 sealer, D4 loader admission, D5 atomic registry, D6 facet grammar/HIR, D7 witness/sidecar, D8 pointcut/weave plan, D9 typed weaver, D10 aspect-pack integration, D11 critical aspect policy, D12 aspect evidence. | `partial` — D2/D3/D4/D5 landed 2026-08-21 (`99.loader/completeness_seal/**`, `check-completeness-seal.shs`); catalog/container/routed-load slice exists (`doc/09_report/aspect_pack_design_coverage_2026-08-18.md`) |
| **3** migration | P1..P12 package shards, one agent per package: census → convert → pin → engine+negative tests → no shared-root edits. | `not started` |
| **4** parallel validation | V1 structural mutation, V2 Any red-team, V3 mono red-team, V4 dynamic red-team, V5 aspect red-team, V6 engine differential, V7 bootstrap parity, V8 fuzz/property, V9 perf/memory, V10 evidence forgery, V11 formal, V12 parallel ownership. | `not started` |
| **5** serial integration + release gate | I0 owns root exports, shared parser dispatch, driver ordering, profile severity table, registry inclusion, release aggregate, default escalation. R1 independently verifies: generated files reproducible, no out-of-scope edits, no bypass env flag honoured in critical, no checker ran advisory under critical, every receipt fresh and bound to artifact+seal hash. | `not started` |

Dependency graph (§21): `Wave 0 → {A1→C*, A2, A4→D2..D5→D6..D12, A5→Y1/Y2→Y3→Y4..Y7, mono
contract→M1→M2/M3→M4/M5/M6→M7/M9, enum contract→S1→S2..S5→S6}` → package migration → red-team /
engine / bootstrap / perf → serial integration → critical release seal.

**Invariant across all waves:** no agent may relax a fail-closed gate before the corresponding
positive *and* negative end-to-end lane is green.

---

## Wire-up

- Requirements: six proposed ids appended to `doc/02_requirements/language/mission_critical_profile.md`
  as a reserved/proposed block (numeric 015–022 untouched).
- Cross-links added to: `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`,
  `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`,
  `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`.

---

## Lane status — landed 2026-08-21 (one-line evidence each)

Status is `partial` unless a whole-tree (not fixture-only) gate is green. Verdict lines are the
last stdout line of each guard; every guard has a fatal `--selftest` and is ERROR on 0 items.

| Lane | Status | Evidence |
|---|---|---|
| A1 schema generator | `done` | `src/app/compiler_schema/{main,registry,extract,coverage}.spl` + `check-compiler-schema-fresh.shs` → `PASS — <n> variant(s) across <k> enum(s), registry fresh`; tests `test/01_unit/app/compiler_schema/` |
| A2 exhaustiveness | `done` | `20.hir/exhaustiveness/coverage_witness.spl` (`coverage_witness_for`, `coverage_witness_code`) + `20.hir/match_coverage.spl` |
| A3 transition model | `done` | `00.common/transition/{transition_table,validator,coverage_state,check_main}.spl`; `check-compiler-transition-coverage.shs` selftest → `PASS — 4 selftest fixture(s) checked across 4 table(s), 0 missing` |
| A4 dynamic identity | `done` | `00.common/dynamic_identity/**` — `freeze_universe`, `dyn_tag`, `claim_of`, `deserialize_to_dense`, `critical_admits` |
| A5 unsafe capability | `partial` | HIR side unlanded — `doc/08_tracking/bug/unsafe_capability_block_syntax_not_parsed_2026-08-21.md` and `unsafe_capabilities_not_carried_into_hir_2026-08-21.md` both OPEN |
| A6 test harness | `done` | `check-hardening-mutation.shs` → `PASS — <n> row(s) checked, 0 missing` (mutation must kill a guard) |
| C2 FlatAst bridge | `done` | `10.frontend/_FlatAstBridge/{convert_nodes,module_assembly}.spl` — silent fallbacks replaced with loud diagnostics |
| C5 HIR→MIR types | `done` | explicit arm per `HirTypeKind` in `50.mir/mir_lowering_types.spl` + `_MirLoweringExpr/expr_dispatch.spl`; gated by `check-critical-wildcard-ban.shs` → `PASS — <n> site(s) checked, forbidden=<k> (baseline <k>)` |
| D2 manifest generator | `done` | `99.loader/completeness_seal/{manifest,axis_parse,required_interfaces}.spl` — `parse_manifest_text`, `required_operations`, `missing_module_interfaces` |
| D3 sealer | `done` | `99.loader/completeness_seal/seal.spl` (`seal_error_code`, `missing_operations`) |
| D4 loader admission | `done` | `99.loader/completeness_seal/admission.spl` — `admit_module` + closed `AdmissionReason` (`E-COMPLETE-021` missing operation, `E-COMPLETE-020` id collision, `E-MC-DYN-001` open `dyn` in critical, `E-COMPLETE-025` seal-hash mismatch, `E-COMPLETE-024` bad axis); no `case _` anywhere |
| D5 atomic registry | `done` | `99.loader/completeness_seal/registry.spl` — build/validate/swap `publish`; a rejected publish leaves the live generation untouched (`E-REGISTRY-001..004`) |
| Phase 5 exit gate | `done` (fixture scope) | `scripts/check/check-completeness-seal.shs` → `PASS — 2 selected constructor(s) checked, missing-capabilities=0 id-collisions=0 dyn-in-critical=0`; `--selftest` → `PASS — 4 selftest fixture(s) checked, scanner detects all three rejection classes`. Decisions come from the real pure-Simple sealer/admission modules via `bin/simple run src/app/check/completeness_seal_census.spl`, never from grepping manifests. Scope is the shipped manifest fixtures under `spec/compiler_schema/extensions/` — D1 (`complete:`/`dyn:` grammar) has not landed, so no whole-tree manifest population exists yet to select from. Specs: `test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl` → `Results: 11 total, 11 passed, 0 failed` |
| M7 post-mono verifier | `partial` | `40.mono/verify/post_mono_verify.spl` + template pruning in `monomorphize_integration.spl`; `check-post-mono-invariants.shs` → `PASS — 9 fixture(s) checked, 0 unexpected` — **fixtures only**, `doc/08_tracking/bug/hir_generic_templates_unconsumed_by_mono_pass_2026-08-21.md` OPEN |
| S2 `@closed` / S3 `@evolving` | `done` | generated attributes on `HirEnum` (`20.hir/hir_definitions.spl`) consumed by `35.semantics/enum_contract/{contract_model,declaration_check,match_check,attribute_source,check}.spl` |
| decorators → HIR | `partial` | filed and being carried: `doc/08_tracking/bug/enum_decorators_dropped_before_hir_2026-08-21.md` |
| step 12 (Any census) | `done` | `35.semantics/any_escape/{checker,types}.spl` (`any_escape_check`) + `check-any-escape-census.shs` → `PASS — <n> module(s) checked, <a> Any site(s), <e> escape(s), <u> unanalyzable (baseline …)` — ratchet baseline, not zero |

Supporting gate added in the same pass: `check-duplicate-pub-fn-names.shs` →
`PASS — 78325 pub fn(s) checked, 1423 colliding name(s) (baseline 1423)`, motivated by
`doc/08_tracking/bug/crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21.md`
(a name collision that produced a **wrong digest** rather than failing).

Whole-tree census remains blocked by
`doc/08_tracking/bug/standalone_hir_lowering_aborts_on_real_compiler_files_2026-08-21.md`;
Phase 7 stays blocked by the four SEGVing stage binaries.

**LLM wiki:** `doc/00_llm_process/feature_expert/compiler_hardening/skill.md` and the
2026-08-21 sections of `layer_expert/{compiler_driver,mir_lowering,bootstrap,test_runner}/skill.md`.
