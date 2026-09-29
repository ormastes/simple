# Domain research: multi-target API gateway configuration

Atlassian Cloud and self-managed deployments use different URL shapes and auth
defaults. Cloud tenants conventionally use an `*.atlassian.net` hostname;
self-managed deployments commonly use custom hosts, ports, and context paths.
Configuration should warn when the declared deployment disagrees with that
shape without silently changing the user's selection.

Enterprise API gateways frequently require routing metadata such as
classification or scope headers. These values belong in named target
configuration, not shell history or source code. Header storage must preserve
ordering and duplicate names, validate against CR/LF injection, and allow an
explicit request header to override configured values case-insensitively.

Secrets and routing configuration have different lifecycles. URLs, deployment
shape, gateway prefixes, and non-secret routing headers belong in
`config.sdn`; bearer tokens, API tokens, passwords, and keys belong in
`auth.sdn` or indirect environment/command sources. Diagnostic redaction must
cover structured headers, URL credentials/query parameters, and both `:` and
`=` assignment syntax before output.
