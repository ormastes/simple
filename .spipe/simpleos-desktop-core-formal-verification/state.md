# SStack State: simpleos-desktop-core-formal-verification

## User Request
> next task from the plan — simpleos_desktop_core_formal_verification (4 lanes: kernel proof, desktop contract, tooling, reporting)

## Task Type
feature

## Refined Goal
> Implement formal verification infrastructure for SimpleOS desktop core: kernel trap/syscall/capability invariant models, desktop selection/focus/crash-containment contract models, verification status tooling scaffolding, and claim/assumption/evidence taxonomy.

## Acceptance Criteria
- [ ] AC-1: Kernel trap model — TrapFrame + SyscallDispatch + PrivilegeSeam with trap-preserves-registers and syscall-returns-to-caller invariants
- [ ] AC-2: Capability authorization — CapGrant + AuthorizationCheck + GrantChain with no-escalation and revocation-propagates invariants
- [ ] AC-3: Scheduler lifecycle — SchedState + LifecycleTransition + LifecycleInvariant with no-zombie-runnable and yield-preserves-context invariants
- [ ] AC-4: Desktop selection uniqueness — SelectionModel + FocusTracker with at-most-one-focused and selection-implies-visible invariants
- [ ] AC-5: Window provenance — WindowProvenance + LauncherBinding with launcher-owns-window and orphan-detection invariants
- [ ] AC-6: Crash containment — CrashPolicy + ContainmentScope + CrashVerdict with crash-doesnt-propagate and default-restart-safe invariants
- [ ] AC-7: Verification status — VerifyStatus + VerifyResult + StatusReport with pass/fail/skip tracking and summary
- [ ] AC-8: Claim policy — VerifyClaim + AssumptionLedger + EvidenceEntry with claim-needs-evidence and assumption-documented invariants
- [ ] AC-9: Evidence taxonomy — EvidenceKind + EvidenceClassification + TaxonomyReport with proof/test/review/assertion categories
- [ ] AC-10: Verification spec — 20 tests covering all 4 lanes

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 4 lanes. Existing: trap_model.spl, app_switcher.spl, shell.spl, crash_policy.spl, qemu_runner.spl, verify/main.spl.

### 5-implement
<pending>
