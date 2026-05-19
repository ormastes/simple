# SStack State: scilib-port-docs

## User Request
> check scilib_port_* plan not done or proper doc or guides. impl with sonnet agent teams with opus advisor.

## Task Type
feature

## Refined Goal
> Bring the scilib port to completion: (1) verify existing implementation actually works (not false-greens), (2) update all 8 plan docs from "PARTIAL/ready" to reflect committed reality, (3) create user-facing guides for std.linalg, std.ndarray, std.df, std.ml.

## Acceptance Criteria
- [ ] AC-1: At least 5 scilib specs produce visible PASS/FAIL output proving assertions run (not silent exit 0)
- [ ] AC-2: All 8 plan docs (perf_sugar, ndarray, blas, lapack, cuda_fortran, math_block, df, ml) have Status updated to reflect implementation state
- [ ] AC-3: User-facing guide exists for std.ndarray + std.linalg (import, create, ops, BLAS/LAPACK usage)
- [ ] AC-4: User-facing guide exists for std.df (DataFrame construction, column ops, groupby, merge, I/O)
- [ ] AC-5: User-facing guide exists for std.ml (LinearRegression, Ridge, metrics, predict)
- [ ] AC-6: Guides are in doc/07_guide/ (not plan docs or tracking)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: feature (docs + verification for existing implementation).
Implementation already landed at commit a7e0cd9c2b (36 files, 4392 insertions) + 7bb9ac0e31 (40 new test specs).
63 spec files exist with 1500+ assertions, but all produce zero output (interpreter false-green risk).
8 plan docs in doc/03_plan/agent_tasks/scilib_port_*.md still show stale "PARTIAL" status.
No user-facing docs/guides exist yet.

Parallel agent plan:
- Wave 1 (disjoint): AC-1 verification agent + AC-2 plan-doc update agent
- Wave 2 (disjoint): AC-3 ndarray/linalg guide + AC-4 df guide + AC-5 ml guide

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
