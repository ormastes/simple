# Dashboard Crash Fix And Systematic Prevention Plan

Date: 2026-04-03
Owner: Codex
Scope: `simple dashboard`, `simple dashboard agents`, dashboard crash containment, dashboard collectors, fallback TODO/plan discovery

## Context

The current dashboard stack is split across Rust and Simple entrypoints.
Research findings from the existing code:

- Rust CLI routing for `simple dashboard` is still stubbed in [misc_commands.rs](src/compiler_rust/driver/src/cli/commands/misc_commands.rs#L467).
- The richer Simple dashboard command surface already exists in [main.spl](src/app/dashboard/main.spl#L20), but it is not reached by the Rust wrapper.
- LLM dashboard entrypoints exist in [llm_dashboard/main.spl](src/app/llm_dashboard/main.spl#L1), with watcher/parser/store plumbing already partially implemented.
- Dashboard collectors still depend on fragile legacy paths in [dashboard_collectors.spl](src/app/dashboard/dashboard_collectors.spl#L1).
- TODO collection currently depends mostly on prebuilt SDN databases and does not have a robust fallback when the DB is missing, stale, or incomplete.

## Goals

1. Fix the dashboard crash path so a dashboard worker failure does not crash the parent session.
2. Make `simple dashboard` use the real dashboard command implementation rather than the Rust placeholder output.
3. Keep `simple dashboard agents` wired through the real LLM dashboard implementation.
4. Make dashboard collection resilient when feature/test/todo/plan DB files are absent or incomplete.
5. Turn the dashboard fix into the proving-ground implementation for the broader crash containment framework.
6. Add source-level TODO and dummy/stub finding so dashboard TODO data is still useful without pre-generated databases.
7. Record progress as work proceeds to reduce restart/crash loss.

## Planned Changes

### 1. Driver Routing

- Replace the hardcoded Rust stub for `handle_dashboard`.
- Delegate to the existing Simple dashboard app entrypoint.
- Preserve argument forwarding for all dashboard subcommands.

### 1b. Dashboard Crash Containment

- Route risky dashboard work through isolated child workers.
- Apply resource limits and supervision uniformly for one-shot and long-running commands.
- Keep the parent dashboard/session process outside the worker fault domain.

### 2. Dashboard Collector Fallbacks

- Update feature DB lookup to prefer current repo paths, including `doc/06_spec/feature_db.sdn`.
- Update test DB lookup to prefer current repo paths while keeping compatible fallbacks.
- Update TODO DB lookup to prefer `doc/todo/todo_db.sdn` and support older paths.
- Update plan/task lookup to support `doc/03_plan/*.md` when task DB data is not present.

### 3. TODO And Dummy Finding

- Add source scanning fallback for:
  - `TODO:`
  - `FIXME:`
  - `pass_todo`
  - `pass_do_nothing`
  - `pass_dn`
- Treat explicit stub markers as dashboard findings when structured TODO DB entries are missing.
- Avoid counting intentional no-op branches as hard TODOs where the surrounding text makes the noop intentional.

### 4. Progress Recording

- Maintain a session progress log with checkpoints before and after each major change.
- Record verification status and any unresolved risks.

## Constraints

- Do not run the dashboard UI/server before the implementation fixes are in place.
- Build, test, and verify the dashboard fix in Docker only; do not rely on current host execution.
- Do not overwrite unrelated user changes in the worktree.
- Prefer narrow edits in existing implementation paths over creating parallel dashboard stacks.

## Verification Plan

1. Run targeted tests for dashboard and LLM dashboard modules in Docker.
2. Run focused command-level verification for dashboard collection/help/status behavior in Docker.
3. Run dashboard crash-containment validation in Docker so worker failure does not kill the parent path.
4. Confirm TODO fallback data is generated from available repo sources when DB files are missing or partial.
5. Update the progress log with pass/fail notes and any residual gaps.
