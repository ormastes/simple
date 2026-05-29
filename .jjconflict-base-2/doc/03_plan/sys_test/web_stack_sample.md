# Web Stack Sample System Test Plan

## Coverage

- Verify backend selection fields exist in the sample config and framework app
  config loader.
- Verify the canonical auth/CRUD/search routes are declared.
- Verify the backend-neutral persistence and dual-backend session abstractions
  are present.
- Verify browser-facing forms and stable UI markers remain explicit.

## Executed Specs

- `test/integration/app/web_stack_sample_spec.spl`
- `test/integration/app/web_stack_sample_browser_spec.spl`
