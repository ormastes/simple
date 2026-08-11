# Bootstrap SDK capsule contract test plan

## Scope

This plan covers the four canonical interfaces and the executable helper
`step_bootstrap_sdk_contract`. It is a preparation contract, not a source
reproducibility, Stage-4 admission, deployment, rollback, or platform
acceptance gate.

## Scenario traceability

The following eleven labels are the complete scenario set. They must remain
identical in this plan, the executable spec, and the manual:

- `CAPSULE-001: canonical interfaces`
- `CAPSULE-002: manifest identity`
- `CAPSULE-003: target and source identity`
- `CAPSULE-004: entry point and modules`
- `CAPSULE-005: module imports and exports`
- `CAPSULE-006: ABI surface`
- `CAPSULE-007: deterministic body archive`
- `CAPSULE-008: compiler and runtime provenance`
- `CAPSULE-009: command host and source provenance`
- `CAPSULE-010: artifact digest binding`
- `CAPSULE-011: preparation claim boundary`

## Assertions

The spec explicitly asserts `SDK-001` through `SDK-010`. It also asserts the
four interface names and the three false claim fields:

```text
reproducibility_evidence=false
stage4_admission_pass=false
platform_acceptance=false
```

The three corresponding true-marker inputs are each passed through a
rejection check. The checks use only built-in non-vacuous matchers such as
`to_contain` and `to_equal`; no placeholder pass is permitted.

## Acceptance and exclusions

Acceptance means that the contract names, requirements, traceability, and
claim boundary are present. It does not establish binary reproducibility,
Stage-4 admission, deployment, rollback, or any x86, ARM, macOS, FreeBSD,
SimpleOS, QEMU, or physical-board acceptance result. Stage 3 is explicitly
outside this test plan.

## Ownership

The executable spec owns observable assertions. The manual owns the reader-
facing flow and claim boundary. The architecture document owns the four
interface definitions. Any change to a scenario label must update all three
artifacts in the same patch.

## Post-bootstrap executable acceptance

After full bootstrap, run `test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl`
once with the exact candidate and adjacent provenance. `PST4-001` through
`PST4-005` cover missing input rejection, canonical identity, source/producer/
Stage 3 lineage, retained hashes, essential-tool receipts, and unchanged smoke.
This proves content identity, not a unique wall-clock build event.
