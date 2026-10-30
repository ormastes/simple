# Bootstrap source-to-object default: selected requirements

Selection authority: the user's explicit request in the 2026-10-24 Windows
Phase 3/4 repair campaign. No option selection remains pending.

- REQ-SOBJ-001: Default Phase 3/4 compilation uses cached source-to-object jobs
  per ready unit. Each job completes HIR, MIR and object work without waiting
  for all source bodies to complete those phases.
- REQ-SOBJ-002: Collect all independently runnable units to terminal outcomes;
  preserve successful objects after sibling failures and block dependent links.
- REQ-SOBJ-003: Use 24 selected jobs for campaign builds/tests, within enforced
  memory admission. Backend threads and frontend processes are distinct budgets.
- REQ-SOBJ-004: Cache use is on by default without an enabling flag, for both
  normal Phase 3/4 source-object builds and explicit step modes. An explicit
  opt-out must be available; it must neither silently disable cache use in
  sibling jobs nor authorize reuse of stale results. Validate producer, original closure,
  declarations/interfaces, dependencies, specializations, options, target/ABI,
  macros, aspects/instrumentation, generated inputs and relevant environment
  effects, storage/runtime authority, post-pass MIR and artifact bytes before
  reuse. Reuse the furthest valid existing result: object, library or final
  binary, with its complete input/context receipt; do not stop at a lower cache
  layer when an unchanged higher artifact is still valid.
- REQ-SOBJ-005: Preserve explicit HIR, MIR and object output/stop modes where
  their existing contracts apply. Provide an explicit split-phase override;
  do not overload `--mode` (currently dynload/one-binary) or change the existing
  `--emit-object`/`--emit-entry-object`/archive/shared output meanings.
- REQ-SOBJ-006: Global declaration and dependency/SCC/specialization sealing is
  required, but no whole-tree HIR/MIR body barrier may implement the default.
- REQ-SOBJ-007: Unsupported producers/capabilities fail visibly. No silent
  fallback to whole-tree compilation under the source-object default label,
  cache rekeying, synthetic declarations or aggregate guard bypass is allowed.
- REQ-SOBJ-008: Prove actual object overlap, real failure collection, unchanged
  cache hits and dependency/context invalidation with native execution before
  enabling the default and claiming completion. Advance generations only after
  the exact producer's real Hello compile/run; full qualification stays distinct.
- REQ-SOBJ-009: Snapshot preparation for the normal build route must complete
  within two seconds. Treat this as an end-to-end measured acceptance target,
  including authority admission, inventory selection and snapshot publication;
  do not report only the final rename as snapshot latency. Cache reuse must
  retain exact source/context invalidation. A slow cold path remains a failed
  performance requirement, not an excuse to bypass source authority checks.

Implementation and evidence remain pending; this document is not a PASS receipt.
