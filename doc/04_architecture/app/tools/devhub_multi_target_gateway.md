<!-- codex-design -->
# DevHub multi-target gateway architecture

## Configuration capsule

`config.spl` owns ordered SDN parsing, Confluence target selection/projection,
provider routing fields, and non-destructive persistence. `ItfConfig` is the
request capsule: origin URL, deployment, complete gateway prefix, ordered
headers, authentication metadata, and (for Confluence) selected target move
together.

Named sections are deliberately limited to `confluence.<name>`. Jira and
Bitbucket use their singleton `jira:` and `bitbucket:` sections. The shared SDN
parser recognizes nested `headers:` entries for all three providers and projects
them into ordered lists without collapsing duplicate names. Flat repeated
`header:` entries remain a read-compatibility form; persistence emits the nested
form.

`auth_token_store.spl` owns section-local `auth.sdn` replacement. A named
Confluence token uses `confluence.<target>` and falls back to the legacy
`confluence` token. Rewriting one credential section preserves every other
section, including provider names unknown to DevHub.

## Provider routing

| Provider | Gateway consumer | Path behavior |
|---|---|---|
| Confluence | `cmd_api.spl`, `adapter_confluence.spl` | Raw relative API paths resolve from the complete prefix; wiki content operations append `/content`. |
| Jira | `cmd_api.spl` with `--jira`; `cmd_jira.spl` through `adapter_jira_curl.spl::JiraClient` | The complete prefix replaces the deployment REST v2/v3 root for raw API requests and normal REST-backed Jira commands. |
| Bitbucket | `adapter_bitbucket.spl`, `adapter_bitbucket_curl.spl` | The Cloud 2.0 or Data Center 1.0 API root is replaced and the resource suffix is retained. Data Center requests under its separate `/rest/build-status/1.0` root are rewritten by the same rule. |

`auth.spl` owns the Confluence/Jira raw-API bases. For normal `devhub jira`
commands, `cmd_jira.spl` projects `jira_gateway_url` and the ordered
`jira_headers` into `JiraClient`; every curl-backed view, search, create,
update, comment, and transition request passes through the client's gateway
argv boundary before `process_run`. The adapter replaces only its deployment
REST root, so unrelated absolute URLs such as attachment downloads remain
direct and do not receive gateway-only headers.

The two Bitbucket clients own their root-rewrite step because their Cloud and
Data Center resources differ. Each recognizes both the deployment's primary
API root and, for Data Center, `{site.base_url}/rest/build-status/1.0`. A commit
status URL such as `/rest/build-status/1.0/commits/{sha}` therefore becomes
`{gateway_url}/commits/{sha}` without losing the resource suffix.

All gateway-capable paths converge on `request_headers.spl` before transport.
That module validates both configured and explicit headers, recognizes gateway
URLs only at a complete prefix boundary, preserves duplicates/order, and
applies case-insensitive explicit raw-API overrides.

## Failure and diagnostic boundaries

Selector parsing is fail-closed. Raw Confluence API requests additionally reject
an unknown explicit target before invoking `rt_http_request`; wiki commands load
an empty capsule and fail authentication before their adapter is reached.
Jira's `--jira` route does not consume a Confluence selector.

`atlassian_site.spl` owns hostname/deployment classification. `cmd_auth.spl`
uses it for Confluence and Jira origin URLs and suppresses only the warning when
`--quiet` or `--silent` is present. Bitbucket status warning output is outside
this feature's implemented surface.

`redaction.spl` is the diagnostic boundary for raw API verbose/error output and
for Confluence/Bitbucket transport failures. Authentication values remain
transport inputs but must not be rendered unmasked.
