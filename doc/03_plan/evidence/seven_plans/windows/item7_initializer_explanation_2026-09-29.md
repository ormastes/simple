# Item 7: adaptive initializer explanation

Date: 2026-09-29. Owner: Codex items3_7 parallel lane.
Requirement: REQ-PSC-006. Status: partial; production verification pending.

The source explanation accepted any method called `new` as proof of the
default adaptive constructor policy. An explicitly typed initializer such as
`val chosen: AdaptiveTextSet = Factory.new()` therefore claimed default
thresholds despite having an unknown factory implementation.

The pure-Simple owner `src/app/optimize/collection_plan_cli.spl` now requires
the initializer receiver to equal the attributed adaptive family and the
constructor to have no arguments. Other initializers keep their unproved
status. Explicit algorithm attributes retain their existing behavior.

Acceptance: reject both factory and instance `new()` as default-policy
evidence; retain the matching `AdaptiveTextSet.new()` positive case.

## Diagnostic TDD evidence

The authorized Phase 1 Windows seed executed
`test/01_unit/app/optimize/collection_plan_cli_spec.spl --mode=interpreter`.
Seed SHA256: `6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
This is a diagnostic, not self-hosted SPipe admission or native evidence.

- Before source edit: 9 examples, 7 passed, 2 failed. The new factory case
  reported `expected true to equal false`.
- After source edit: 9 examples, 8 passed, 1 failed. Factory/instance rejection
  and the genuine constructor control passed.
- The pre-existing collision profile case remains failing: expected
  `profile.hash_collisions_p95=40`, observed `100`. Its cause is unproven;
  the assertion was retained. No additional retries were made.
- A separate minimal metric-envelope diagnostic was rejected by profile
  admission before producing measurements. It does not localize the remaining
  failure. The third bounded investigation cycle ended without another fix.

Logs: `C:/Users/User/dev/simple-items3-7-red.log` and
`C:/Users/User/dev/simple-items3-7-green.log` (local diagnostic artifacts).
The inconclusive metric probe log is
`C:/Users/User/dev/simple-items3-7-metric.log`.

## Completion boundary

Item 3 declares 11 functional requirements; item 7 declares 8. Neither has
complete Windows or Linux/WSL certification. Source includes typed logical
plan models, an extractor, guarded selector, adaptive storage, profile
admission, and initial-plan explanation. The extractor currently has no
production call site in the inspected compiler pipeline; the explanation
explicitly reports `guard.typed_mir=unconnected`. Full typed extraction,
physical MIR lowering, cross-engine proofs, and NFR evidence remain open.
These are requirement inventories, not implementation percentages.

The new regression manual is authored from executable cases; docgen and
admitted self-hosted verification remain outstanding. This change must not
be labeled a seven-item completion or verification PASS.
