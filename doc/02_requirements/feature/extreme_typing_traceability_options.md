# Extreme typing and traceability: requirement options

Status: mixed scope inventory and remaining architecture options, 2026-11-01.
The [selected extreme-typing addendum](extreme_typing_traceability.md) records
the user's all-builtins, semantic-bound-generics and easy nominal creation
decision. Those decisions are closed. The existing [20 traceability requirements](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md#41-normative-requirements)
remain authoritative. Requested extension capabilities are selected; remaining choices concern implementation policy only. Delete unchosen options when recording
the decisions; do not claim they have already been selected.

Selected REQ-TRC-021..032 and REQ-EAPI-001..009 live in the [requirement addendum](extreme_typing_traceability.md). Their acceptance mapping is in the [test plan](../../03_plan/sys_test/extreme_typing_traceability.md). No acceptance-test-to-unit-test relationship is introduced.

## Decisions required before dependent implementation

Effort is a relative implementation estimate: S = a few focused days; M = one
to two engineer-weeks; L = several weeks with migration/parity work. Estimates
are not delivery promises and exclude bootstrapping unrelated runtime failures.

| Decision | Option A: benefit; cost; effort | Option B: benefit; cost; effort | Blocked phase |
|---|---|---|---|
| D1 group declaration placement | Extend canonical `doc/08_tracking/trace` declarations: central ownership and migration; larger manifests; M. | Colocate SDN group manifests with requirement/feature owners: locality; more discovery and negative-cache dependencies; M. | P1 persisted group authoring |
| D2 fixing identity | Immutable repository+commit OID fixes a bug; PR is attributable metadata: stable offline truth; squash/backport mapping needs explicit origin; M. | Typed ChangeSet includes commit and versioned PR-head/merge snapshots: richer workflow; mutable PR identity must never stand in for immutable code; L. | P3/P10 fixing claims |
| D3 coverage-role eligibility | Preserve current acceptance/nonacceptance split and add a versioned policy role table: compatibility; some specialized roles stay unknown pending classification; M. | Explicit roles per obligation (system/performance/security included): precise intent; more authoring and migration; L. | P4 new role qualification |
| D8 migration | Package-by-package opt-in policy pins with moderate/strict inventory before robust admission: reviewable scope; mixed-profile ecosystem and dependency boundaries need tracking; L. | Coordinated release-wide cutover after complete migration inventory: uniform guarantee; high compatibility cost and longer critical path; L. | E3 rollout/release |

Closed decisions D4..D7: all true builtin scalars are covered; exposed generics
require a semantic-domain-safe bound; easy nominal creation and existing typed
literal forms are first-class migration requirements; raw ABI declarations stay
private behind typed Simple facades. No public Simple FFI escape is offered.
Foreign linker ABI exports, if needed, require a separately reviewed contract
and cannot weaken the public Simple guarantee.

Raw pointers and `any` are a separate unsafe-exposure rule, not ordinary scalar
aliases. The scalar decision does not silently decide that rule's exemptions.
Transparent aliases remain rejected when they expose prohibited primitives;
nominal newunit/opaque types are eligible only if their public operations and
constructors do not reopen the raw boundary. Neither naming conventions nor
`@allow(primitive_api)` grant an extreme-API exemption.

Decision record template: decision ID, chosen option or exact alternative,
owner/date, affected requirement IDs, migration boundary and acceptance cases.
The architecture can be reviewed now; these rows block only dependent code.
