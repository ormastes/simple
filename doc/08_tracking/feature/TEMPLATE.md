# Feature Tracking Entry Template

Add new feature work to `feature_db.sdn` through the tracking tooling or by
following this row shape exactly.

```text
features |id, group, device, component, title, description, status, priority, source_file, requirement, research, plan, architecture, design, system_spec, spec_doc, implementation, unit_tests, integration_tests, guide, external_system, external_id, external_url, last_synced_at, created_at, updated_at, valid|
    FR-AREA-0001,area,device,component,"Short title","Observable request or feature summary",request,P2,doc/08_tracking/feature/source.md,,,,,,,,,,,,github,,https://github.com/org/repo/issues/1,,YYYY-MM-DD,YYYY-MM-DD,true
```

## Status

- `request`: proposed or imported.
- `current`: accepted, active, or implemented elsewhere without full local
  pipeline evidence.
- `done`: complete and linked through the required pipeline artifacts.
- `blocked`: waiting on an external dependency.
- `rejected`: closed without implementation.

## Done Evidence

Before setting `status=done`, fill:

`requirement`, `research`, `plan`, `architecture`, `design`, `system_spec`,
`spec_doc`, and `implementation`.

Fill `unit_tests`, `integration_tests`, and `guide` when the feature scope
requires them.
