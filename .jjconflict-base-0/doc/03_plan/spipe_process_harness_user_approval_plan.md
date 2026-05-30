# SPipe Process Harness Official Plan

Date: 2026-05-15
Status: official implementation and verification plan

## Objective

Build and maintain a production-level SPipe process harness for Codex, Claude,
and Gemini. The harness provides one shared hook contract, provider-specific
deployment snippets, durable process state, approval/prevention gates, and a
compact CLI HUD for operator context.

This file is the official plan for the SPipe process harness. The shorter
agent-task list remains at `doc/03_plan/agent_tasks/spipe_process_harness.md`,
but this plan is the source of truth for scope, requirements, implementation
phases, verification, and remaining production work.

## Approved Scope

The user approved full scope on 2026-05-15:

- Shared hook infrastructure for Codex, Claude, and Gemini.
- Raw provider payload preservation through normalized JSONL event envelopes.
- Provider-specific deploy snippets generated from one shared implementation.
- Per-skill hook integration through the common harness contract.
- CLI HUD showing model, jj worktree, commit, hours remaining, week remaining,
  and current goal.
- Durable goal/process state in `.spipe/<feature>/state.md`.
- Prevention gates that return a hook-compatible non-zero exit code when
  approval or required state is missing.

## Requirements Trace

- REQ-001: common hook infrastructure for Codex, Claude, and Gemini.
- REQ-002: normalize provider hook payloads into append-only JSONL events.
- REQ-003: generate deploy snippets for all three providers from one shared
  implementation.
- REQ-004: CLI HUD shows model, jj worktree, commit, hours remaining, week
  remaining, and goal.
- REQ-005: persist goal/process state in `.spipe/<feature>/state.md`.
- REQ-006: prevent unsafe progress when approval or state gates are missing.
- NFR-001: hook path is fast and append-only.
- NFR-002: shared logic is testable without invoking provider CLIs.
- NFR-003: prevention failures return a non-zero hook-compatible exit code.
- NFR-004: HUD output remains one compact CLI line.
- NFR-005: unrelated worktree changes are excluded from SPipe commits.

## Artifact Map

- Local research: `doc/01_research/local/spipe_process_harness.md`
- Domain research: `doc/01_research/domain/spipe_process_harness.md`
- Feature requirements: `doc/02_requirements/feature/spipe_process_harness.md`
- NFR requirements: `doc/02_requirements/nfr/spipe_process_harness.md`
- Architecture: `doc/04_architecture/spipe_process_harness.md`
- Detail design: `doc/05_design/spipe_process_harness.md`
- TUI design: `doc/05_design/spipe_process_harness_tui.md`
- System test plan: `doc/03_plan/sys_test/spipe_process_harness.md`
- Agent task plan: `doc/03_plan/agent_tasks/spipe_process_harness.md`
- System spec: `doc/06_spec/app/spipe_process_harness/feature/spipe_process_harness_spec.spl`
- Durable example state: `.spipe/spipe-process-harness/state.md`
- CLI entrypoint: `src/app/spipe_process_harness/main.spl`
- Library API: `src/lib/nogc_async_mut/spipe_process_harness/`
- Unit tests: `test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl`

## Architecture Plan

### Layer 1: Shared Data Contracts

Owned files:

- `src/lib/nogc_async_mut/spipe_process_harness/types.spl`

Contracts:

- `GateDecision`: allow/block result and hook exit code.
- `HudSnapshot`: model, jj context, remaining time, and goal.
- `HookDeploySnippet`: provider name, target path, and generated snippet body.

### Layer 2: Pure Harness Core

Owned files:

- `src/lib/nogc_async_mut/spipe_process_harness/core.spl`
- `src/lib/nogc_async_mut/spipe_process_harness/mod.spl`

Responsibilities:

- Normalize provider names and payloads.
- Render append-only JSONL hook events.
- Render durable state files.
- Evaluate approval/prevention gates.
- Render one-line HUD output.
- Generate Codex, Claude, and Gemini deploy snippets.

The hot hook path must avoid repository-wide scans, provider subprocess calls,
or network access. It should only normalize input, read the selected state file,
append one event, and return an allow/block exit code.

### Layer 3: CLI Surface

Owned files:

- `src/app/spipe_process_harness/main.spl`
- `src/app/cli/dispatch/table.spl`

Commands:

- `state`: create or refresh `.spipe/<feature>/state.md`.
- `hook`: read provider payload from stdin, gate it, append JSONL, and return
  the provider-compatible exit code.
- `gate`: evaluate durable state without appending an event.
- `hud`: print compact operator context.
- `deploy`: write generated provider hook snippets under `.spipe/hook-deploy/`.

## Implementation Phases

1. Requirements and design: keep the approved full-scope requirements, NFRs,
   architecture, detail design, TUI design, and test plan current.
2. Core library: maintain provider normalization, event rendering, state
   rendering, gate decisions, HUD rendering, and deploy snippet generation.
3. CLI integration: maintain command dispatch for `spipe_process_harness` and
   keep commands scriptable for provider hooks.
4. State and deploy artifacts: keep `.spipe/<feature>/state.md` and generated
   deploy snippets deterministic and reviewable.
5. Tests: maintain system-level spec coverage and unit coverage for provider
   normalization, deploy snippets, HUD, state, and gates.
6. Verification: run focused checks/tests before every commit and document any
   repository-wide smoke warnings separately from SPipe scope.
7. VCS sync: commit on `main`, fetch, rebase linearly, keep file-count guard,
   push only `main`.

## Verification Gates

Required focused checks:

```bash
bin/release/simple check \
  src/lib/nogc_async_mut/spipe_process_harness/*.spl \
  src/app/spipe_process_harness/main.spl \
  test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl \
  doc/06_spec/app/spipe_process_harness/feature/spipe_process_harness_spec.spl

SIMPLE_LIB=src bin/release/simple test \
  test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl \
  --mode=interpreter --clean
```

Required quality scans:

- No placeholder pass helpers, placeholder assertions, deferred-only comments,
  or empty implementation bodies in SPipe harness source, specs, or tests.
- All `.spl` files remain under the 800-line guard.
- CLI dispatch stays registered and points to
  `src/app/spipe_process_harness/main.spl`.

## Current Implementation Status

Implemented:

- Shared provider normalization for Codex, Claude, and Gemini.
- Append-only normalized hook event rendering.
- Deploy snippets for all three providers.
- Durable state rendering and approval/prevention gate decisions.
- One-line HUD rendering.
- CLI entrypoint and dispatch registration.
- Unit and system specs for the approved feature scope.

Known boundaries:

- `deploy` writes reviewable snippets; it does not overwrite live provider
  config files directly.
- Provider hook blocking semantics differ, so the harness standardizes its own
  exit-code contract and leaves provider-specific installation to the generated
  snippets.
- The current implementation is local-file based; no network service is
  required for the hook path.

## Production Feature Requests

### SPH-PROD-001: Live Provider Config Installer

Add an opt-in installer that can patch Codex, Claude, and Gemini live config
files after showing a diff. Acceptance: no config overwrite without explicit
confirmation, backup files are created, and generated snippets remain available
for manual review.

### SPH-PROD-002: Event Replay And Debug Tooling

Add replay commands for `.spipe/<feature>/events.jsonl`. Acceptance: operators
can replay normalized events against gate logic, inspect raw payloads, and
compare allow/block decisions across harness versions.

### SPH-PROD-003: Skill-Level Policy Profiles

Add per-skill policy profiles for approval requirements, gate strictness, and
provider hook modes. Acceptance: policy files are deterministic, missing policy
falls back to conservative defaults, and tests cover conflicting policies.

### SPH-PROD-004: HUD Runtime Evidence

Add measured HUD latency and hook hot-path latency smoke tests. Acceptance:
representative hook and HUD commands stay below documented local latency
targets and avoid repeated full-tree scans.

### SPH-PROD-005: Multi-Workspace Goal Reconciliation

Add explicit reconciliation for multiple jj workspaces sharing one SPipe goal.
Acceptance: stale workspace heads are detected, active workspace identity is
shown in HUD, and gate output identifies which workspace owns the current goal.

## VCS Policy

- Work directly on `main`.
- Do not create long-lived branches or orphan commits.
- Do not leave child workspaces registered unless they are actively needed.
- Cherry-pick useful worktree commits onto `main` when they are current and in
  scope.
- If a worktree commit is wrong, stale, or unrelated, do not cherry-pick it;
  document that decision in the sync summary.
- Before push: fetch, rebase onto `main@origin`, check tracked file count did
  not unexpectedly drop, then push `main`.

## Completion Definition

The SPipe process harness plan is complete for the approved local MVP when:

- All approved requirements and NFRs map to implementation and tests.
- Focused SPipe harness checks/tests pass.
- Stub and placeholder scans are clean.
- Docs and plan files identify production-level remaining work.
- The final commit is on `main`, linearly rebased, and pushed.
