<!-- codex-design -->
# DevHub multi-target gateway detail design

## Configuration shape

Named sections use `confluence.<name>:`. Jira and Bitbucket remain singleton
provider sections. All three accept the canonical nested header form:

```sdn
confluence.internal:
    gateway_url: https://gateway.example/confluence
    headers:
        X-Classification: Internal
        X-Scope: A
        X-Scope: B

jira:
    gateway_url: https://gateway.example/jira
    headers:
        X-Classification: Restricted

bitbucket:
    gateway_url: https://gateway.example/bitbucket
    headers:
        X-Classification: Internal
```

The parser treats each child of `headers:` as one ordered `Name: Value` entry,
so duplicate names survive. Flat repeated `header: Name: Value` lines are still
read. Persistence writes nested maps.

## Selection and persistence

Confluence selection precedence is one explicit `--host`/`--profile` selector,
`confluence.default_target`, the first named section, then the legacy singleton.
More than one selector, a missing selector value, or an explicit name with no
matching target is rejected before raw API transport. The wiki path reaches the
same no-network outcome through its authentication gate.

Target-scoped Confluence credential lookup checks indirect environment/command
sources and `confluence.<target>` in `auth.sdn`, then legacy sources. Config save
replaces the selected named Confluence section while retaining the default and
sibling named blocks. Credential save replaces exactly one section and retains
sibling and unknown sections.

## URL and header composition

`gateway_url` is a complete provider API prefix:

- Confluence raw API resolves relative paths against it; wiki operations append
  `/content` and carry configured headers on GET/POST/PUT/DELETE.
- Jira raw API (`api --jira`) uses it instead of the normal deployment REST
  root. `cmd_jira.spl` also copies the gateway and ordered headers into its
  `JiraClient`, so REST-backed view/search/create operations and the
  update/comment/transition curl fallbacks use the same route.
- Bitbucket replaces its deployment API root with it and preserves the resource
  suffix for both native and curl client transports. A Data Center
  `/rest/build-status/1.0/commits/{sha}` URL is a second recognized origin root
  and resolves to `{gateway_url}/commits/{sha}`.

Configured headers are considered only when the final URL equals the gateway
prefix or begins with its `/` or `?` boundary. Header names must be non-empty,
and names/values containing CR or LF are rejected. On the raw API surface,
explicit repeated `--header` entries remove all configured entries with the same
case-insensitive name, then retain their own order. Absolute direct URLs receive
only explicit headers.

For the three client adapters, transport preparation is ordered:

1. Build the direct provider URL and transport argv, including authentication.
2. Replace only a recognized provider root with the normalized gateway prefix.
3. Validate and append configured headers only when the resolved URL is within
   the gateway prefix boundary.
4. Invoke the transport with the resolved URL as the final argv entry.

Jira's recognized root is its Cloud REST v3 or Data Center REST v2 root.
Bitbucket recognizes its Cloud REST 2.0/Data Center REST 1.0 primary root plus
the Data Center build-status 1.0 root. Unrelated Jira downloads and Bitbucket
URLs remain unchanged and receive no gateway-only configured headers.

## Warnings and redaction

Auth status compares the parsed hostname of the configured Confluence and Jira
origin URL—not arbitrary path text and not the gateway hostname—with the
declared deployment. A mismatch produces a warning; `--quiet` and `--silent`
return an empty warning without changing any configuration.

Before diagnostics are printed, redaction masks Authorization, Cookie,
Set-Cookie, conventionally secret header names, URL user-info and sensitive
query values, JSON/SDN-like assignments, and both `:`/`=` separators. Raw API
verbose output and transport errors, Confluence curl stderr, and both Bitbucket
transport error paths use this boundary.
