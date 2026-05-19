# SStack State: simpleos-desktop-core-formal-verification

## User Request
> next task from the plan — simpleos_desktop_core_formal_verification (4 lanes: kernel proof, desktop contract, tooling, reporting)

## Task Type
feature

## Refined Goal
> Implement formal verification infrastructure for SimpleOS desktop core: kernel trap/syscall/capability invariant models, desktop selection/focus/crash-containment contract models, verification status tooling scaffolding, and claim/assumption/evidence taxonomy.

## Acceptance Criteria
- [x] AC-1: Kernel trap model — TrapFrame + SyscallDispatch + PrivilegeSeam with trap-preserves-registers and syscall-returns-to-caller invariants
- [x] AC-2: Capability authorization — CapGrant + AuthorizationCheck + GrantChain with no-escalation and revocation-propagates invariants
- [x] AC-3: Scheduler lifecycle — SchedState + LifecycleTransition + LifecycleInvariant with no-zombie-runnable and yield-preserves-context invariants
- [x] AC-4: Desktop selection uniqueness — SelectionModel + FocusTracker with at-most-one-focused and selection-implies-visible invariants
- [x] AC-5: Window provenance — WindowProvenance + LauncherBinding with launcher-owns-window and orphan-detection invariants
- [x] AC-6: Crash containment — CrashPolicy + ContainmentScope + CrashVerdict with crash-doesnt-propagate and default-restart-safe invariants
- [x] AC-7: Verification status — VerifyStatus + VerifyResult + StatusReport with pass/fail/skip tracking and summary
- [x] AC-8: Claim policy — VerifyClaim + AssumptionLedger + EvidenceEntry with claim-needs-evidence and assumption-documented invariants
- [x] AC-9: Evidence taxonomy — EvidenceKind + EvidenceClassification + TaxonomyReport with proof/test/review/assertion categories
- [x] AC-10: Verification spec — 20 tests covering all 4 lanes

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 4 lanes. Existing: trap_model.spl, app_switcher.spl, shell.spl, crash_policy.spl, qemu_runner.spl, verify/main.spl.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/os/kernel/verify/kernel_proof_model.spl — TrapFrame + SyscallDispatch + CapGrant + AuthorizationCheck + SchedState + LifecycleTransition
- src/os/desktop/verify/desktop_contract_model.spl — SelectionModel + FocusTracker + WindowProvenance + CrashPolicy + CrashVerdict
- src/os/kernel/verify/verify_status.spl — VerifyResult + StatusReport + VerifyStatus
- src/os/kernel/verify/evidence_taxonomy.spl — VerifyClaim + AssumptionLedger + EvidenceEntry + EvidenceClassification + TaxonomyReport
- test/unit/os/formal_verification_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
