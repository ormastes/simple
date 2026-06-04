# Tracking

`doc/08_tracking/` contains live project tracking data. The canonical core
trackers are DB-first and use generated Markdown for review.

| Kind | Source of truth | Generated/readable output | Purpose |
|------|-----------------|---------------------------|---------|
| bug | `bug/bug_db.sdn` | `bug/recent_bugs.md` | Defects, regressions, release blockers |
| feature | `feature/feature_db.sdn` | `feature/feature.md`, status and group pages | Feature requests, current work, done records |
| test | `test/test_db.sdn`, `test/test_db_runs.sdn` | `test/test_result.md` | Test inventory and run history |
| task | `task/task_db.sdn` | `task/task.md` | Human/agent execution work |
| todo | `todo/todo_db.sdn` | `../TODO.md` | Code TODO/FIXME scan results |

Other folders under this tree are supporting evidence or legacy notes. New
tracking categories should be modeled as one of the five core kinds first.

## Feature Done Gate

A feature row may use `status=done` only when the row links the required
pipeline artifacts:

`requirement`, `research`, `plan`, `architecture`, `design`, `system_spec`,
`spec_doc`, and `implementation`.

Unit tests, integration tests, and guide links are filled when applicable. Run:

```bash
bin/simple tracking check --kind=feature
```

## External Sync

Local SDN/text DBs remain usable offline. GitHub is the primary external task
system and is represented through:

`external_system`, `external_id`, `external_url`, `last_synced_at`

Use explicit commands for external movement:

```bash
bin/simple tracking export --target=github
bin/simple tracking import --target=github
bin/simple tracking sync --target=github --kind=feature
```

Hooks never sync to external systems automatically.
