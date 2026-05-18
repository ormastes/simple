# SStack State: vhdl-subprogram-emission

## User Request
> next task from the plan — vhdl_subprogram_emission (function/procedure lowering, entity selection, naming/mangling, diagnostics)

## Task Type
feature

## Refined Goal
> Implement VHDL subprogram emission models: function lowering for single-return helpers, procedure lowering for multi-output helpers, entity-vs-subprogram selection criteria, VHDL name sanitization with collision detection, and emission diagnostics for stateful/cycle/unsupported constructs.

## Acceptance Criteria
- [ ] AC-1: SubprogramKind — kind enum (function/procedure/entity), selection reason, is_combinational flag
- [ ] AC-2: FunctionLower — helper name, return type, parameter list, is_pure flag, VHDL function signature
- [ ] AC-3: ProcedureLower — helper name, out-parameter list, in-parameter list, multi-return count
- [ ] AC-4: SubprogramDecision — helper ref, chosen kind, rejection reason, fallback to entity flag
- [ ] AC-5: VhdlSanitizedName — original name, sanitized name, was_modified flag, collision index
- [ ] AC-6: CollisionCheck — name pair, is_collision flag, resolution strategy (suffix/prefix/index)
- [ ] AC-7: StatefulCheck — helper name, has_state flag, state kind (signal/variable/process), diagnostic message
- [ ] AC-8: CycleDetection — caller, callee, is_cycle flag, cycle depth
- [ ] AC-9: EmissionDiagnostic — diagnostic kind, helper name, message, severity (error/warning)
- [ ] AC-10: Verification spec — 20 tests covering lowering, selection, naming, diagnostics

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across function/procedure/entity lowering, naming, diagnostics. Existing: vhdl_builder.spl, vhdl_helpers.spl.

### 5-implement
<pending>

### 7-verify
<pending>
