# Item 5 implementation acceptance scaffold

Status: **criteria and test skeletons authored; every scenario NOT_IMPLEMENTED**.

This is the criteria-first phase requested on 2026-10-03. It covers seven work
packages within item 5, not the other six items of the umbrella plan. It does not
add feature implementation, compiler admission, runtime verification, or fixes.

The selected [requirements](../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md)
and the existing [I5-01 through I5-14 plan](item5_provider_size_acceptance_2026-10-02.md)
remain authoritative. Existing partial code and unit tests do not mark these
broader acceptance scenarios complete.

| Package | Acceptance list | SSpec skeleton | Criteria | Requirement coverage |
|---|---|---|---:|---|
| P01 Platform and policy admission | [criteria](item5_pending/p01_platform_admission.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p01_platform_admission_spec.spl) | 8 | REQ-002, REQ-012 |
| P02 Immutable artifact mapping | [criteria](item5_pending/p02_immutable_mapping.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p02_immutable_mapping_spec.spl) | 8 | REQ-002, REQ-012, REQ-013, REQ-015 |
| P03 First demand, concurrency and lifetime | [criteria](item5_pending/p03_demand_lifetime.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p03_demand_lifetime_spec.spl) | 9 | REQ-001, REQ-002, REQ-011, REQ-012, NFR-005 |
| P04 Packaged CLI activation | [criteria](item5_pending/p04_packaged_cli.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p04_packaged_cli_spec.spl) | 10 | REQ-003, REQ-011, REQ-012, REQ-015 |
| P05 Exact closure and profiles | [criteria](item5_pending/p05_closure_profiles.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p05_closure_profiles_spec.spl) | 10 | REQ-003, REQ-007 through REQ-011, REQ-013 |
| P06 Size and startup | [criteria](item5_pending/p06_size_startup.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p06_size_startup_spec.spl) | 10 | REQ-014, NFR-001 through NFR-004, NFR-007 |
| P07 Selection, parity and promotion | [criteria](item5_pending/p07_selection_parity.md) | [spec](../../../test/03_system/runtime/provider/item5_pending/p07_selection_parity_spec.spl) | 14 | REQ-004 through REQ-006, REQ-011, REQ-012, NFR-006; I5-14 ownership |

Total: **69 acceptance criteria and 69 matching skeleton scenarios**. Together
the packages retain REQ-001 through REQ-015 and NFR-001 through NFR-007.

## Authoring contract

Each package's acceptance list was written before its SSpec skeleton. Every
criterion has a stable `I5-Pnn-ACnn` ID, requirements, setup, action, observable
result and explicit NOT_IMPLEMENTED status. Scenarios use `describe`, `it` and
three readable planned `step(...)` statements, followed by
`fail("NOT_IMPLEMENTED <criterion>: ...")`.

The `in-development` tag uses the existing runner convention for work in
progress. The additional `not-implemented` tag is a descriptive authoring label.
Explicit scenario execution is intended to fail until the body is implemented;
no empty body, no-op, `pass_todo`, synthetic assertion or helper PASS hides the
missing behavior. Planned steps perform no setup or product operation.

Replace a failure marker only when its real production setup, action and
observable assertions exist. Remove work-in-progress status only for implemented
scenarios; do not convert missing fixtures or evidence to success. No runtime
execution, RED/GREEN, coverage, generated manual, feature completion or release
qualification is claimed by this scaffold.

## Parallel ownership

- `item5_research`: P01/P02, isolated closure worktree.
- `item5_tdd_audit`: P03/P04, isolated loader worktree.
- `item5_cli`: P05/P06, isolated CLI worktree.
- Parent: P07, shared conventions, criteria review and scaffold-only integration.

Only these new acceptance documents and test skeletons belong to this change.
Earlier unverified implementation work remains a separate change.
