<!-- codex-design -->
# System test plan: LLM Caret infrastructure access

## Scope

Executable spec:
`test/03_system/app/llm_caret/feature/llm_caret_spipe_infra_access_hardening_spec.spl`.
Generated/manual output mirrors it under `doc/06_spec/03_system/app/llm_caret/feature/`.

## Helpers

- `input(provider, operation, args, format)` constructs tool JSON.
- `expect_supported_plan` checks route identity, safety, program, and argv.
- `expect_capability_error` checks fail-closed unsupported behavior.
- `expect_permission_denied` checks no provider runner marker was produced.
- `recording_runner` returns deterministic provider-shaped output while
  recording the exact plan it received.

## Coverage matrix

| Area | Requirements | Evidence |
|---|---|---|
| registration/gate | 001, 010, 011 | known names; read/write/destructive decisions; no shell program |
| repo/task | 002-004, 008 | GitHub, Bitbucket, Jira plans and unsupported rows |
| storage/mail/wiki | 005-008 | S3/MinIO, Gmail/Outlook, Confluence/GitHub Wiki plans |
| normalized evidence | 009, 012 | injected runner proves exact plan and stable result |
| documentation | 013, 014 | executable doc block and generated manual links |
| security/NFR | all NFRs | offline determinism, path/secret rejection, streaming file routes, diagnostic cap, performance sample |

Every REQ appears in at least one executable `describe`/`it` name. Provider
contract tests are offline. Optional live tests are not counted as normal CI
success and must identify their actual route.

The opt-in live matrix is
`test/03_system/e2e/llm_caret_infra_access_live_spec.spl`. Enable one row with
`LCSI_LIVE_<PROVIDER>=1` and provide only non-secret resource argv through
`LCSI_LIVE_<PROVIDER>_ARGS`; authentication stays in the canonical CLI store or
environment. Each executed row retains provider, adapter, transport, safety,
status, elapsed microseconds, and destructive-grant state. Write/destructive
live tests are intentionally absent until a disposable fixture contract is
configured.

## Acceptance

- Focused unit and system specs pass once.
- Branch coverage of new compatibility code is at least 80%.
- Docgen succeeds and the manual contains the seven step strings; until the
  tracked nested-`split` compiler defect is fixed, the mirrored manual companion
  must contain them and must disclose that it was not generator-produced.
- Direct runtime guard and placeholder/stub scans pass.
- The local plan/permission benchmark p95 is below 200 ms.
