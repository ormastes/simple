# Feature Tracking

Feature tracking records feature requests, current feature work, and done
feature evidence. Requirements still live under `doc/02_requirements/feature/`;
this folder tracks workflow state and external task-system links.

## Files

| File | Purpose |
|------|---------|
| `feature_db.sdn` | Source of truth for feature tracking rows |
| `feature.md` | Generated group/status index |
| `request_feature.md` | Generated requested-feature list |
| `current_feature.md` | Generated current-work list |
| `done_feature.md` | Generated done-feature list |
| `group/*.md` | Generated per-group/device/component pages |
| `TEMPLATE.md` | Manual row/entry guidance |

## Lifecycle

`request` means the feature is proposed or imported from GitHub/another task
system. `current` means accepted or actively being worked. `done` is reserved
for rows with complete pipeline evidence. `blocked` and `rejected` are terminal
or waiting states with a note in the description or external issue.

`done` requires these fields to be populated:

`requirement`, `research`, `plan`, `architecture`, `design`, `system_spec`,
`spec_doc`, and `implementation`.

Run `bin/simple tracking check --kind=feature` before marking a row done.

## GitHub And Other Systems

GitHub is the primary external task system. Store external references in
`external_system`, `external_id`, `external_url`, and `last_synced_at`.

Other task managers should use the same fields and adapter shape. Do not add a
new local tracking folder for each external system.
