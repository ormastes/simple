# DevHub multi-target gateway requirements

The user selected the following requirements on 2026-09-14. “Named target” in
this feature means a named Confluence target; Jira and Bitbucket retain their
singleton provider sections while participating in the common gateway policy.

- REQ-001: Confluence supports multiple named targets selected by exactly one
  non-empty `--host` or `--profile` selector. Missing values, conflicting
  selectors, and unknown explicit targets fail before network transport.
- REQ-002: When no Confluence selector is supplied, the configured
  `confluence.default_target` wins; otherwise the first named target in file
  order wins, followed by the legacy singleton fallback.
- REQ-003: Confluence, Jira, and Bitbucket each carry ordered, repeated
  arbitrary HTTP headers. The canonical SDN form is a nested `headers:` map;
  repeated flat `header: Name: Value` entries remain accepted for compatibility.
- REQ-004: Confluence, Jira, and Bitbucket may each define a complete
  `gateway_url`. Confluence raw API/wiki traffic, Jira raw API traffic and the
  normal `devhub jira` REST transport constructed by `cmd_jira.spl`, and both
  Bitbucket client transports route through their provider gateway while
  preserving the resource-path suffix. For Bitbucket Data Center, this includes
  the separate `/rest/build-status/1.0` root used for commit-status requests.
  Routing stays in `config.sdn` and secrets stay in `auth.sdn` or indirect token
  sources.
- REQ-005: Configured provider headers are attached only after a request
  resolves under that provider's configured gateway. On raw API requests,
  repeated explicit `--header` values replace configured values with the same
  case-insensitive name while retaining order and unrelated configured headers.
- REQ-006: `devhub auth status` warns when the configured Confluence or Jira
  origin hostname shape disagrees with its declared Cloud/Data Center
  deployment. `--quiet` and `--silent` suppress these warnings without changing
  routing or authentication state.
- REQ-007: Verbose and transport-error diagnostics redact Authorization,
  Cookie/Set-Cookie, URL credentials and sensitive query values, and sensitive
  `token|key|secret|password` assignments using either `:` or `=`. Confluence
  and Bitbucket adapter stderr crosses the same redaction boundary.
- REQ-008: Config updates preserve the configured Confluence default and
  sibling named Confluence targets, including nested repeated headers.
  Credential updates replace only their owned `auth.sdn` section and preserve
  sibling and unknown credential sections.
