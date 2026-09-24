# DevHub multi-target gateway system-test plan

## Scope

Trace REQ-001 through REQ-008 across target selection/defaulting, nested and
repeated headers, provider gateway routing, explicit header overrides,
deployment warnings/suppression, redaction, and non-destructive config/auth
persistence. Gateway scope includes raw Jira API calls, normal JiraClient-backed
commands, Bitbucket primary API roots, and the separate Bitbucket Data Center
build-status root. Network behavior is tested at pure URL/header/argv and fake
command-transport boundaries; live enterprise gateways are excluded.

## Execution

1. Run focused unit specs for config, request headers, gateway URL/argv,
   deployment warnings, API composition, redaction, and persistence.
2. Run the feature system spec under the admitted runtime.
3. Generate its mirrored manual with `spipe-docgen --no-index`; require zero
   stubs and manually inspect visible scenario steps.
4. Run working/staged numbered-artifact and direct-env guards.

## Pass criteria

- Every REQ has happy, edge, and fail-closed evidence across the referenced
  focused/system specs.
- Invalid selectors and CR/LF headers reach no transport.
- Gateway classification headers appear only when the resolved URL uses the
  configured gateway.
- Normal REST-backed Jira commands carry the configured gateway and ordered
  headers into `JiraClient` before curl transport.
- Data Center build-status URLs in both Bitbucket transports rewrite
  `/rest/build-status/1.0/commits/{sha}` to `{gateway_url}/commits/{sha}`.
- No sensitive value appears in diagnostic output.
- Saving one target/provider preserves sibling sections and repeated values.

## Traceability

| Requirement | Implementation | Primary executable evidence |
|---|---|---|
| REQ-001 | `config.spl`, `cmd_api.spl`, `cmd_wiki.spl`, `cmd_auth.spl` | `itf_config_spec.spl`, feature system spec |
| REQ-002 | `config.spl` | `itf_config_spec.spl`, feature system spec |
| REQ-003 | `config.spl`, `request_headers.spl` | `itf_config_spec.spl`, `request_headers_spec.spl`, feature system spec |
| REQ-004 | `auth.spl`, `cmd_api.spl`, `cmd_jira.spl`, `adapter_jira_curl.spl`, `adapter_confluence.spl`, both Bitbucket adapters | `itf_api_spec.spl`, `cmd_jira_spec.spl`, `adapter_jira_curl_spec.spl`, `confluence_gateway_spec.spl`, `adapter_bitbucket_spec.spl`, `adapter_bitbucket_curl_spec.spl`, feature system spec |
| REQ-005 | `request_headers.spl` and provider transport callers | `request_headers_spec.spl`, `itf_api_spec.spl`, `confluence_gateway_spec.spl`, both Bitbucket adapter specs, feature system spec |
| REQ-006 | `atlassian_site.spl`, `cmd_auth.spl` | `atlassian_site_spec.spl`, feature system spec |
| REQ-007 | `redaction.spl`, `cmd_api.spl`, Confluence/Bitbucket adapters | `redaction_spec.spl`, `redaction_auth_document_spec.spl`, `redaction_followup_spec.spl`, `redaction_comma_spec.spl` |
| REQ-008 | `config.spl`, `auth_token_store.spl` | `itf_config_persistence_spec.spl`, `itf_config_spec.spl`, feature system spec |

The generated/manual mirror is
`doc/06_spec/03_system/app/devhub/feature/devhub_multi_target_gateway_spec.md`.
Scenario steps are visible; implementation code is folded/detail-only. No UI
or screenshot capture is required. Command/config output uses `text` evidence.

## Remaining verification gaps

- Exercise the real `auth status --quiet` and `--silent` command paths; current
  evidence proves the warning helper and static command wiring.
- Exercise an unknown/conflicting selector through raw API and wiki command
  dispatch and assert that the transport is not invoked; current evidence proves
  selector parsing plus the source-level pre-transport guards.
- Feed secret-bearing stderr through the Confluence and both Bitbucket transport
  wrappers; current evidence proves the redactor and source-level wrapper calls
  separately.
- Run the focused specs and feature system spec under the admitted runtime, then
  regenerate this feature's manual with `0 stubs`. This docs-only audit does not
  claim those executions passed.
