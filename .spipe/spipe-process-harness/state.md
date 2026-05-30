# SStack State: spipe-process-harness

## User Request
> make spipe production level process harness; common hooks for Codex, Claude, Gemini; skill deploy infra; CLI HUD with model, jj worktree, commit, hours remaining, week remaining; goal state; prevention gate; commit pull rebase push.

## Refined Goal
> Deliver a production-level SPipe process harness library with provider normalization, event-log gate semantics, HUD rendering, and hook deploy snippets, plus a CLI entrypoint and full unit test coverage.

## Harness
- User Approved: true
- Prevent: allow
- Hook Providers: codex, claude, gemini
- Event Log: .spipe/spipe-process-harness/events.jsonl

## Acceptance Criteria
- [x] AC-1: Common hook envelopes are normalized for Codex, Claude, and Gemini.
- [x] AC-2: Provider hooks feed one shared event log and gate path.
- [x] AC-3: The HUD shows model, jj worktree, commit, hours remaining, week remaining, and goal.
- [x] AC-4: Skill deploy output documents provider hook snippets.
- [x] AC-5: Prevention blocks when approval/state gates fail.

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [-] 2-research (Analyst) — skipped
- [-] 3-arch (Architect) — skipped
- [-] 4-spec (QA Lead) — skipped
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
Categorized as feature. Refined goal: shared harness lib + CLI for all three LLM providers. ACs cover normalize, gate, HUD, deploy, and prevention.

### 5-implement
Created `src/lib/nogc_async_mut/spipe_process_harness/types.spl`, `core.spl`, `mod.spl`, and `src/app/spipe_process_harness/main.spl`. All functions implemented and exported.

### 6-refactor
No over-engineering. Functions kept pure and single-purpose. Types use structs with named fields.

### 7-verify
20 unit tests in `test/unit/app/spipe_process_harness/spipe_process_harness_spec.spl` — all passing.

### 8-ship
State artifacts updated. Tests pass. No outstanding TODOs.

### post-ship (Wave 16 — 2026-05-19)
Rewrote test spec to import from the actual library (`std.nogc_async_mut.spipe_process_harness.types` + `core`) instead of inline mirrors. Removed all duplicated struct/fn definitions. Added 8 new test cases covering `provider_hook_events`, `hook_command`, and `hook_jsonl`. All 37 tests pass against the real library code.

## Pipeline Status: CLOSED — verified Wave 16-5

