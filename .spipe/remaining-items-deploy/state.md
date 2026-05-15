# SStack State: remaining-items-deploy

## User Request
> make remains in new agents teams plan. fix limitation after research. recheck untracked files add to tracked file and commit pull rebase and push

## Task Type
todo

## Refined Goal
> Complete three remaining post-bootstrap tasks: (1) Create an agent teams plan document organizing remaining work items (Stage 3 SEGFAULT fix, 7 non-critical type-inference skips, untracked files), (2) Research and fix the Stage 3 SEGFAULT/exit-139 LLVM constructor conflict (LIM-010), (3) Add all 57 untracked source files to git, commit, pull/rebase from origin, and push.

## Acceptance Criteria
- [ ] AC-1: Agent teams plan document created at `doc/03_plan/remaining_agent_teams_plan.md` covering Stage 3 fix, non-critical file fixes, and future work items
- [ ] AC-2: Stage 3 SEGFAULT (LIM-010) researched — root cause documented, fix applied or limitation formally recorded with mitigation
- [ ] AC-3: All 57 untracked files in `src/compiler/{40.mono,50.mir,55.borrow,60.mir_opt}` and `src/lib/{editor,ffi,format_utils.spl,gc_async_mut}` added to git tracking
- [ ] AC-4: Changes committed with descriptive message via jj
- [ ] AC-5: Pull/rebase from origin/main successful, push completed

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-15
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** todo (post-bootstrap cleanup + deploy)

**Refined goal:** Three parallel work streams:
1. **Plan doc** — organize remaining work into agent team assignments
2. **LIM-010 research** — Stage 3 SEGFAULT is documented in `doc/09_report/bootstrap_crash_report_2026_04_01.md`. Root causes: LLVM constructor double-registration, `Box::leak` context accumulation, missing `--entry-closure`. Current mitigation: Cranelift backend + non-fatal stage 3. Need to assess if a real fix is feasible.
3. **Untracked files** — 57 files across 6 directory groups need tracking + commit + push

**Acceptance criteria confirmed:** 5 ACs as listed above.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
