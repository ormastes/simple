# SStack State: vhdl-subprogram-emission

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — vhdl_subprogram_emission (function/procedure lowering, entity selection, naming/mangling, diagnostics)

## Task Type
feature

## Refined Goal
> Implement VHDL subprogram emission models: function lowering for single-return helpers, procedure lowering for multi-output helpers, entity-vs-subprogram selection criteria, VHDL name sanitization with collision detection, and emission diagnostics for stateful/cycle/unsupported constructs.

## Acceptance Criteria
- [x] AC-1: SubprogramKind — kind enum (function/procedure/entity), selection reason, is_combinational flag
- [x] AC-2: FunctionLower — helper name, return type, parameter list, is_pure flag, VHDL function signature
- [x] AC-3: ProcedureLower — helper name, out-parameter list, in-parameter list, multi-return count
- [x] AC-4: SubprogramDecision — helper ref, chosen kind, rejection reason, fallback to entity flag
- [x] AC-5: VhdlSanitizedName — original name, sanitized name, was_modified flag, collision index
- [x] AC-6: CollisionCheck — name pair, is_collision flag, resolution strategy (suffix/prefix/index)
- [x] AC-7: StatefulCheck — helper name, has_state flag, state kind (signal/variable/process), diagnostic message
- [x] AC-8: CycleDetection — caller, callee, is_cycle flag, cycle depth
- [x] AC-9: EmissionDiagnostic — diagnostic kind, helper name, message, severity (error/warning)
- [x] AC-10: Verification spec — 20 tests covering lowering, selection, naming, diagnostics

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across function/procedure/entity lowering, naming, diagnostics. Existing: vhdl_builder.spl, vhdl_helpers.spl.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/compiler/70.backend/backend/vhdl/vhdl_subprogram_model.spl — SubprogramKind + FunctionLower + ProcedureLower + SubprogramDecision
- src/compiler/70.backend/backend/vhdl/vhdl_subprogram_naming.spl — VhdlSanitizedName + CollisionCheck + SanitizedParam + MangledSignature
- src/compiler/70.backend/backend/vhdl/vhdl_subprogram_diag.spl — StatefulCheck + CycleDetection + EmissionDiagnostic + DiagnosticReport
- src/compiler/70.backend/backend/vhdl/vhdl_subprogram_select.spl — SelectionCriteria + EntityKeep + SubprogramCandidate + EmissionPlan
- test/unit/compiler/vhdl_subprogram_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
