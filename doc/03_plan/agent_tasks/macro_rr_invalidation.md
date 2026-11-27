<!-- fable-design -->
# Macro RR invalidation — agent task breakdown

Frozen interface names are in `doc/05_design/compiler/macro_rr_invalidation.md` §1–§3
(`macro_rr_contract_v1`, `macro_rr_inventory_v1`, `macro_rr_invalidation_v1`). No agent may
rename a subject prefix, family, struct field, or widen reason without updating the design and
the spec guide in the same PR.

| # | Lane | Model | Scope | Output |
|---|---|---|---|---|
| 1 | Research + architecture + design + test plan | Fable (lane owner) | this doc set | `doc/01_research/local/macro_rr_invalidation.md`, `doc/04_architecture/compiler/macro_rr_invalidation.md`, `doc/05_design/compiler/macro_rr_invalidation.md`, `doc/03_plan/sys_test/macro_rr_invalidation.md` |
| 2 | SSpec guide (failing first) | Opus sidecar | unit / integration / system specs per the test plan; `step("...")` sentences, `@req` ids REQ-MACRO-RR-001..010, built-in matchers only, no placeholder passes | `test/01_unit/compiler/cache/macro_rr_*_spec.spl`, `test/02_integration/compiler/cache/macro_rr_invalidation_edit_rebuild_spec.spl`, `test/03_system/compiler/feature/macro_rr_invalidation_spec.spl` |
| 3 | Shared contract PR (lands first) | Fable | `00.common/cache_contract/macro_rr_contract_v1.spl` + its unit spec | PR A |
| 4 | Driver inventory + invalidation + `incremental.spl` wiring | Fable | `80.driver/cache/macro_rr_inventory_v1.spl`, `macro_rr_invalidation_v1.spl`, `incremental.spl`, `action_key.spl`, `module_artifacts_v1.spl` | PR B |
| 5 | Build/test runs | Haiku sidecars | exact commands from the test plan on `bin/release/<triple>/simple`; report `Results:` lines verbatim; coverage numbers | evidence in PR bodies |
| 6 | PR review | Opus sidecar | zero P0/P1 on each PR diff | review comments |
| 7 | Manuals + plan status | Fable | `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`; plan §1A.0 row | PR C |

Sidecar lanes: Haiku runs only; Opus writes specs and reviews. Merge owner: lane owner (Fable).
Final reviewer: Opus review of each PR diff before `gh pr merge --admin --merge`; the lane owner
answers every finding or fixes it. Coordination with `generic-rr`: fetch `origin` before each PR;
the shared contract (task 3) lands before any driver wiring so the generic lane can fold its facet
into the same identity frame.
