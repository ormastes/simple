# Shared collection capability and DataFrame selection TDD plan

**2026-10-27 — PLAN / UNRUN.** Extends existing selected item 3/7 and async
requirements. This document creates no executable tests and reports no RED,
GREEN, coverage, performance or host qualification. Its scenarios must be
implemented before the corresponding production changes; never add passing
placeholder bodies. [Normative contract](../../04_architecture/compiler/collection_backend_capabilities.md).

Reuse existing executable owners:
`test/01_unit/compiler/mir_opt/collection_plan_selection_spec.spl`,
`test/01_unit/lib/nogc_async_mut/df_typed_series_checked_spec.spl`,
`test/03_system/app/compiler/feature/collection_planner_columns_spec.spl`,
`collection_planner_mir_spec.spl`, `profile_switchable_typed_plan_acceptance_spec.spl`
in that system directory, and existing runtime adaptive/async resource specs.
Do not create another DSL, test scheduler, or fixture-only native certificate.

Shared proposed helpers: `collection_capability_setup_fixture`,
`collection_capability_run_actual`, `collection_capability_compare_reference`.
Use `step("capture reference behavior")`, `step("execute admitted backend")`,
`step("compare behavior and capabilities")`. Unimplemented helpers must fail
explicitly; they cannot construct success receipts. Models use an independent
array/trace oracle, and production runs prove actual provider/lowering identity.

| ID | Requirement crosswalk / real stimulus | Independent oracle and required failure control |
|---|---|---|
| CBC-01 | PSC-AC-001/005; SRH-17/18/46: strict multicore request with ordinary Hash, DashMap, legacy mutex and owner-local candidates | Unsupported before effects; no locked/provider fallback. Inject false capability or route to legacy ABI and require call-path/native audit failure |
| CBC-02 | PSC-AC-002; SRH-01/14: all eligible value maps on collisions, zero/extreme i64, text, nil, NaN/signed-zero where supported; registry pending/error controls | Exact reference values/order/errors, and explicit noninterchangeability for unsupported equality/value contracts. Change key equality or confuse nil with absent; test must fail |
| CBC-03 | PSC-AC-003/004; AIF/SRH progress gates: disabled/unavailable metrics, available capture with static-only selection, missing profile | Availability and reasons distinct from measured zero; no fake selected change. Native instrumentation proves disabled strict lookup never enters capture mutex; force capture and fail |
| CBC-04 | PSC-AC-001/002/006: constructor-only backend, no-switch metadata, unsupported directed migration, ABI-pinned/ExternalFixed/Never layout | Explicit request diagnostic or advisory Original with reason; source stays unchanged; a tag cannot fabricate migration support. Force transition and require mismatch |
| CBC-05 | CP-001/004/009; S7-I03-AC02/03/07: typed columns and indexes across permitted layout/backend pairs | Values, masks, dtype errors, strides/reversed views, duplicate chains, row order, missing/nil, NaN/signed-zero match checked reference. Drop mask/reorder duplicate chain and fail |
| CBC-06 | CP-003/008/009; PSC-AC-005: callbacks throw, mutate alias, short-circuit or suspend; unknown key/layout proofs | Exact callback/result/error trace; inadmissible fusion/join/index keeps Original. Force cost/profile override of a failed proof and fail |
| CBC-07 | CP-010/011; PSC-AC-004/005/008: change source generation, key semantics, target, backend, layout, policy, profile and registry independently | Only compatible receipts admitted; explain matches actual MIR and executed provider. Fake executed receipt from advisory decision must fail |
| CBC-08 | SRH-21/22/23; CVC-RES-07: reader retains old container while new map/layout publishes, evicts, retires or suspends | Protected old value or typed owner/generation failure, no bucket/ordinal reinterpretation; remove retained ownership and fail race/lifetime gate |
| CBC-09 | CP-009; SRH-16/35: allocation failure, conversion failure, overflowing bounds, full byte budget including old+new+retired copies | Old committed value intact; peak within cap or typed rejection; unknown is not zero. Exclude retained bytes from accounting and fail |
| CBC-10 | SRH-02/03/05/08/16; CVC-SCALE: 3,000 same-key refs, 3,000 distinct index keys, cancellation, pending epoch transition | Exact outcomes; one ordinary maker per exact recipe/attempt; independent producer progress within budgets; no slot loss or duplicate producer. Count physical attempts separately from accepted publication |
| CBC-11 | S7-I03-AC09/11; S7-I07-AC08: same fixture through qualified native and later pure-Simple providers | Common interface semantics and actual import/provider binding agree; native pass does not certify pure Simple or another target. Deliberate wrong adapter/provider is detected |
| CBC-12 | CP NFR-001–007; PSC NFR; SRH-42/43: geometric/skew/collision inputs, permitted transitions, static/unprofiled controls | Equivalent output before timing; real build/probe/output/transition counts, startup/preallocation/tail/RSS and retirement included. n×m outputs counted; no fabricated winner or hidden profiler cost |

CBC refines existing criteria rather than renumbering them. Required mappings:
S7-I03-AC02/03/06/07/08/09/10/11 and S7-I07-AC01–08 all retain their broader
scope. Existing semantic registry, compiler P0, native atomic/SimpleRing,
SOSIX publication, SCV and bootstrap gates remain independent requirements.

For each slice: commit/retain real behavioral RED on the production owner;
implement the smallest change; run focused GREEN once; refactor and run only
affected checks; retain source/provider/target/fixture/oracle identities and
exact test inventory. Parser/linker/runner unavailability is infrastructure
failure, not the intended RED. Keep model, interpreter, bootstrap and native
evidence distinct. Do not relabel skeleton cases, skipped providers, advisory
plans or a successful process exit as completed execution. Native contention,
ABA/lifetime, allocation and no-lock audits require real native providers.

Limit this feature to six verify/fix cycles across sessions and worktrees,
with a changed cause or new evidence per retry; never rerun unchanged passing checks. Existing
per-host and performance policies remain binding; this plan adds no new
numerical threshold or default enablement.
