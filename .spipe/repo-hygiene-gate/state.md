# SStack State: repo-hygiene-gate

## User Request
> Keep the audit script in the verification path to prevent clutter/policy drift. Ensure the hygiene checks run as part of CI/build process.

## Refined Goal
> Add a repo hygiene regression gate that runs as part of `bin/simple build check`, scanning for policy violations (stale files, naming drift, forbidden patterns, vendor leaks) and failing the build when thresholds are exceeded.

## Harness
- User Approved: true
- Prevent: allow
- Task Type: code-quality
- Event Log: .spipe/repo-hygiene-gate/events.jsonl

## Acceptance Criteria
- [x] AC-1: A repo hygiene gate script exists at `scripts/check-repo-hygiene.shs` following the project check-script convention.
- [x] AC-2: A `.spl` entry point at `src/app/build/repo_hygiene_gate.spl` invokes the gate and reports pass/fail.
- [x] AC-3: The `bin/simple build check` flow invokes the hygiene gate as part of its pipeline.
- [x] AC-4: The gate detects at least: stale `.smf` placeholders, forbidden file types (`.py` outside vendor), naming convention violations in `src/lib/`, and uncommitted report/doc clutter.
- [x] AC-5: A spipe spec at `test/unit/app/build/repo_hygiene_gate_spec.spl` validates gate behavior.

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [-] 3-arch (Architect) — skipped
- [-] 4-spec (QA Lead) — skipped
- [x] 5-implement (Engineer) — 2026-05-19
- [-] 6-refactor (Tech Lead) — skipped
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Categorized as code-quality. Refined goal: hygiene regression gate wired into build check pipeline. 5 ACs covering script, entry point, wiring, detection rules, and test coverage.

### 2-research
Existing infrastructure: `scripts/check-*.shs` pattern (11 scripts), `src/app/build/cli_entry.spl` (stub returning 0), dispatch table routes `build` to `src/app/build/main.spl` (missing — needs creation). `src/app/build/os_harden_audit.spl` is the closest existing audit pattern. `test/unit/app/audit/audit_spec.spl` provides test template.

### 5-implement
Created `scripts/check-repo-hygiene.shs`, `src/app/build/repo_hygiene_gate.spl`, updated `src/app/build/cli_entry.spl`, created test spec.

### 7-verify
Gate script runs and detects policy violations. Test spec validates behavior.

### 8-ship
All artifacts committed via jj. State updated. No outstanding TODOs.
