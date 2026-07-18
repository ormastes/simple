# Web Stack Sample System Test Plan

## Coverage

- Verify backend selection fields exist in the sample config and framework app
  config loader.
- Verify the canonical auth/CRUD/search routes are declared.
- Verify the backend-neutral persistence and dual-backend session abstractions
  are present.
- Verify a seeded SimpleDB-backed sample app can be reopened by a second process
  with the same user, item, and session-visible state.
- Verify browser-facing forms and stable UI markers remain explicit.

## Executed Specs

- `test/02_integration/app/web_stack_sample_spec.spl`
- `test/02_integration/app/web_stack_sample_browser_spec.spl`
- `test/02_integration/app/web_stack_sample_persistence_spec.spl`
