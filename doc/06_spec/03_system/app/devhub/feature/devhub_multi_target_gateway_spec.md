# DevHub multi-target gateway configuration

This manual mirrors
`test/03_system/app/devhub/feature/devhub_multi_target_gateway_spec.spl` and
traces REQ-001 through REQ-008.

## Select a target

Named selection applies to Confluence. Use either `--host NAME` or
`--profile NAME`, but not both. With neither, DevHub uses the configured
default, then the first named target, then the legacy singleton. Missing,
conflicting, and unknown explicit selectors fail before network transport.
Jira and Bitbucket continue to use their singleton provider sections.

## Configure routing

Confluence, Jira, and Bitbucket can each define a complete `gateway_url` and an
ordered nested `headers:` map. Duplicate header names remain ordered; legacy
flat repeated `header:` entries are also read. CR/LF-bearing configured or
explicit headers are rejected.

Configured classification headers are attached only when the resolved request
uses the configured gateway. On raw Confluence/Jira API calls, repeated explicit
`--header` values override configured entries with the same case-insensitive
name. An absolute URL outside the gateway receives only explicit headers.

Confluence uses the gateway for raw API and wiki content operations. Jira uses
it for raw `api --jira` traffic and for normal REST-backed `devhub jira`
commands through the configured `JiraClient`. Bitbucket replaces its Cloud or
Data Center primary API root in both client transports while preserving the
resource path. Data Center build-status requests also replace their separate
`/rest/build-status/1.0` root, so `/commits/{sha}` remains intact behind the
gateway prefix.

## Keep routing separate from credentials

Store URLs, deployment shape, gateway prefixes, and routing headers in
`config.sdn`. Store target-scoped tokens in `auth.sdn` or indirect environment
and command sources. Saving one target/provider preserves sibling sections.

## Diagnose safely

`devhub auth status` warns when a Confluence or Jira origin hostname shape
disagrees with the configured Cloud/Data Center deployment. `--quiet` and
`--silent` suppress the warning only. Verbose diagnostics mask
Authorization/Cookie fields, URL secrets, and token/key/secret/password
assignments using `:` or `=`. Confluence and Bitbucket transport stderr is
passed through the same redactor.

## Executable evidence

The executable system spec checks selectors and loads real isolated `config.sdn`
fixtures to prove that `confluence.default_target` wins over file order and that
the first named target wins when no default exists. It also checks nested
duplicate headers, injection rejection, Jira/Confluence/Bitbucket gateway
resolution, gateway-only classification policy, deployment warnings, and secret
masking.

The REQ-008 scenario uses the production config/auth load and save helpers
against isolated real files. It reopens the default target and reads both files
from disk to prove that the configured default, sibling named target, repeated
headers, sibling credential, and unknown credential section survive an update.
Raw API header composition, four-verb Confluence argv behavior, Jira
command-to-client transport composition, and both Bitbucket transport paths
(including Data Center build status) remain in focused unit specs.

This manual describes the implemented contract but does not itself certify a
runtime pass. The system-test plan records the remaining command-dispatch,
adapter-stderr, admitted-runtime, and docgen verification gates.
