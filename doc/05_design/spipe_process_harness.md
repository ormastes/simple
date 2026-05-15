<!-- codex-design -->
# SPipe Process Harness Detail Design

## Data Structures

- `GateDecision`: allow/block result and hook exit code.
- `HudSnapshot`: model, jj worktree, commit, remaining hours/week, and goal.
- `HookDeploySnippet`: provider, target path, and generated snippet body.

## Commands

- `state`: creates durable `.spipe/<feature>/state.md`.
- `hook`: reads provider hook payload from stdin, gates, and appends JSONL.
- `gate`: verifies state and approval.
- `hud`: prints one-line status.
- `deploy`: writes provider snippets to `.spipe/hook-deploy/`.

## Error Handling

Missing state or missing approval returns exit code `2`, matching hook block semantics used by existing diagnostics comments.

