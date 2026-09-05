# Dashboard Completion Progress

Date: 2026-04-03
Owner: Codex
Related plan: `doc/03_plan/dashboard_completion_and_todo_fix_2026-04-03.md`

## Checkpoints

- [x] Research current dashboard and TODO implementations.
- [x] Identify the active blocker: Rust `simple dashboard` handler is still a stub.
- [x] Identify collector path drift and missing fallback logic.
- [x] Patch Rust dashboard routing to execute the real dashboard implementation.
- [x] Add framework-level worker budget export for dashboard crash containment.
- [ ] Patch Simple dashboard collectors to use current/fallback repo paths.
- [ ] Add source fallback for TODO and dummy/stub findings.
- [ ] Verify dashboard and TODO behavior with targeted tests/commands.

## Research Notes

- `simple dashboard` currently returns placeholder text from Rust instead of calling the richer Simple app command handler.
- `simple dashboard agents` exists in the Simple app, but is hidden behind the Rust stub.
- `src/app/dashboard/dashboard_collectors.spl` reads old DB locations directly and has no broad fallback scan.
- `doc/todo/todo_db.sdn` exists and should be preferred for TODO data.
- `doc/03_plan/` contains plan markdown that can be used when task DB rows are absent.
- Container verification on 2026-04-03 confirmed the mounted-workspace release binary still panics in `tracing_appender::rolling::daily(...)` when `.simple/logs` is not writable.
- New dashboard framework policy tests pass in the Docker isolation image, including the worker budget shell export path.
- Compose files had drifted to `docker/Dockerfile.*`; the real repository path is `tools/docker/`.
- Rebuilding the current bootstrap Rust binary inside Docker succeeded on 2026-04-03.
- The next live blocker is startup/runtime cost: `simple dashboard help` still times out after 60s inside Docker with no stdout/stderr, so the CLI path is reachable but not yet usable.

## Next Step

Investigate why the dashboard entrypoint does not complete in Docker even for `help`. The most likely follow-up is reducing startup work or switching the wrapper to a cached compiled artifact path, then resuming collector/TODO fallback hardening.
