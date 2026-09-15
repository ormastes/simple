# DevHub multi-target gateway implementation plan

Updated: 2026-09-14

## Objective

Deliver switchable multi-host Confluence configuration plus Confluence, Jira,
and Bitbucket gateway routing across raw and normal client transports, ordered
multi-value headers, gateway-only header injection, deployment-shape warnings,
and comprehensive diagnostic secret redaction. Publish through a feature
branch/PR and merge only after `STATUS: PASS`.

## Current authoritative state

- Worktree: `C:\devhub-fix`
- Branch: `fix/devhub-confluence-config`
- Remote commits: `c98a2a5070f`, `0f54ff9fbd4`
- Pull request: `#990` (open; CI queued/pending at last poll)
- Astra final working-tree review: `STATUS: PASS` after the all-provider routing,
  persistence evidence, and redaction follow-ups were completed.

## Completed implementation

- [x] Named Confluence targets selected by `--host`/`--profile`.
- [x] Configured default target and first-named-target fallback.
- [x] Target-scoped credentials in separate `auth.sdn`, with legacy fallback.
- [x] Ordered repeated headers, CR/LF validation, and explicit override policy.
- [x] Nested `headers:` maps plus flat repeated `header:` compatibility for
  Confluence, Jira, and Bitbucket.
- [x] Confluence gateway routing and header-aware GET/POST/PUT/DELETE transport.
- [x] Jira gateway base and gateway-only headers on raw `api --jira` requests
  and on normal REST-backed `devhub jira` commands through the configured
  `JiraClient` transport.
- [x] Bitbucket Cloud/Data Center primary API gateway rewriting plus separate
  Data Center build-status root rewriting and gateway-only headers in both
  Bitbucket transports.
- [x] Gateway classification headers on raw API gateway requests, with explicit
  case-insensitive override and no leakage to absolute direct URLs.
- [x] Deployment/URL mismatch warning with `--quiet`/`--silent`.
- [x] Verbose and transport-error redaction for headers, URLs, bodies, `:` and
  `=` assignments, including Confluence and Bitbucket stderr boundaries.
- [x] Unknown/conflicting Confluence raw API selectors fail before transport.
- [x] Config persistence uses the `app.io.mod` read/existence/write facade and
  credential persistence preserves unknown sections.
- [x] Feature system SPipe, mirrored manual, system-test plan, trace matrix, and
  local/domain research companions exist.
- [x] Early branch commits pushed and PR opened for remote-agent collaboration.
- [x] Direct-env working/staged audits, layout check, and stub scan passed before PR.

## Verification evidence retained

- Confluence gateway behavior: 3 Phase-1 examples passed.
- Raw API/header behavior: 14 Phase-1 examples passed.
- Deployment-shape helper: 2 examples passed.
- Redaction follow-ups: final Phase-1 regression set passed 7/7, including
  multiline/prefixed secrets, RFC 3986 userinfo punctuation, and multiple URLs.
- Feature system SPipe: final permitted Phase-1 cycle passed 14/14, including
  default/first target resolution and real filesystem persistence.
- Astra final static review: `STATUS: PASS`.
- Focused executable evidence exists for `cmd_jira` config-to-`JiraClient`
  routing and for native/curl Bitbucket Data Center build-status gateway argv;
  these additions still require admitted-runtime execution below.

## Remaining verification and delivery work

- [ ] Run the asserted persistence spec in a fresh verification session; do not
  exceed the prior three-cycle cap in this session.
- [ ] Add or retain executable command-dispatch evidence for real
  `auth status --quiet/--silent` behavior and selector no-transport behavior.
- [ ] Add or retain adapter-level assertions that secret-bearing Confluence and
  Bitbucket stderr is redacted, not only unit evidence for the redactor.
- [ ] Run the focused provider/header/redaction specs and the feature system
  spec under the admitted runtime.
- [ ] Regenerate/validate the mirrored manual with `spipe-docgen --no-index` and
  require `0 stubs`.
- [x] Run working/staged numbered-artifact and direct-env guards.
- [ ] Commit/push the current hardening/evidence changes and refresh PR #990.
- [ ] Wait for CI, resolve branch-related failures, rebase on current `main`, and obtain
  final `STATUS: PASS`.
- [ ] Merge PR #990 only after all required checks and verification pass.

## Stop conditions

Stop and report instead of looping when any acceptance criterion has already passed in
this session, when one criterion reaches three verify/fix cycles, or when CI remains
queued without an actionable failure. Never merge while verification is FAIL/WARN.
