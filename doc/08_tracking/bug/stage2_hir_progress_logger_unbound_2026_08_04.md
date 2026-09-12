# Stage 2 HIR progress logger is unbound

**Status:** OPEN (unverified 2026-09-12)

## Status

Resolved on 2026-08-04.

## Reproduction

The strict x86 Phase 4 bootstrap reached Stage 2 and failed at link time in
`driver_hir_pipeline_lowering` with two undefined references to
`log_build_progress`. The HIR cadence change added calls, but the integrated
tree contained neither a public helper definition nor an explicit import.

## Repair

Restore the canonical append-only progress helper in `driver_log_helpers`,
including cached `SIMPLE_BUILD_PROGRESS_EVENTS` lookup and token escaping, and
import that free function explicitly in the HIR lowering module. The helper is
a no-op when no receipt path is configured. It is not a `CompilerDriver`
method and is not replaced by the environment-gated phase logger.

## Regression

`test/01_unit/compiler/driver/hir_progress_cadence_contract_spec.spl` checks
the helper export, the split-module import, both HIR call sites, and the
16-module cadence.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
