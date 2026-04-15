# Traceability Guide

Use this when writing requirement-driven tests and companion docs.

## Direction

- Feature and system specs point to requirements.
- Plan, design, architecture, and research docs point back to requirements.
- If a prose doc needs to point to tests, point to generated markdown under `doc/06_spec/`, not raw `test/..._spec.spl`.

## Required Spec Header

For `test/feature/**` and `test/system/**`, include:

```markdown
**Requirements:** doc/02_requirements/feature/<slug>.md
**Plan:** doc/03_plan/<slug>.md
**Design:** doc/05_design/<slug>.md
**Research:** doc/01_research/<slug>.md
```

- Use `N/A` only when the link is intentionally absent.
- Prefer plain relative paths in spec headers.
- Use the same slug across related docs when possible.

## Requirement Coverage

- Requirement and NFR docs should contain stable `REQ-*` or `NFR-*` identifiers.
- Feature/system specs linked to that document should reference the identifiers they cover.
- If a requirement doc has identifiers that no linked spec references, `simple traceability-check` emits a warning.

## Source To Test Mapping

The checker can also enforce source-to-test mapping for opted-in roots from `config/traceability.sdn`.

- Source file expectation: sibling logical unit spec under `test/unit/.../<name>_spec.spl`
- Module expectation: each `__init__.spl` or leaf source directory has an integration/module spec under `test/integration/...`

This rollout is opt-in for existing code to avoid turning legacy layout drift into thousands of warnings at once.

## Commands

```bash
simple traceability-check
simple traceability-check --scope=spec
simple traceability-check --format=json
simple build --warn-docs
```
