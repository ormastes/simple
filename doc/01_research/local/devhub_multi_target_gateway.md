# Local research: DevHub multi-target gateways

DevHub configuration is owned by `src/app/devhub/config.spl`. Before this
feature, `ItfConfig` held one Confluence URL/user and flat Jira/Bitbucket
settings. `load_config()` parsed a small SDN subset into section/key/value
triples. Credentials were already stored separately in
`~/.config/itf/auth.sdn`, but token save logic knew only fixed provider names.

Confluence wiki operations flow through `cmd_wiki.spl` into
`adapter_confluence.spl`. Raw REST requests flow through `cmd_api.spl` and
`rt_http_request`. The Confluence adapter uses a curl argv builder; all verbs
converge on `_confluence_request`. Deployment-specific URL/auth behavior is
centralized in `atlassian_site.spl` and `auth.spl`.

The original verbose API path masked only the Authorization scheme and printed
custom headers, URLs, bodies, and some errors directly. Auth status had no
URL/deployment mismatch diagnostic. Config parsing did not preserve nested
header maps, named targets, or arbitrary named credential sections.

Primary implementation risks are complete `ItfConfig` reconstruction,
non-destructive SDN persistence, consistent gateway/header policy across raw
API and adapters, and applying redaction at every diagnostic boundary.
