# DevHub multi-target gateway detail design

Named sections use `confluence.<name>:`. Repeated `header: Name: Value` lines represent a multi-map without collapsing duplicate names. Selection precedence is explicit selector, `confluence.default_target`, first named section, then legacy singleton.

The gateway URL is a complete API prefix. Confluence content operations append `/content`; raw API resolves relative paths against the prefix. Configured target headers are attached only on gateway routing, validated for non-empty names, and rejected on CR/LF. Explicit repeated `--header` values replace configured entries with the same case-insensitive name.

Credential lookup checks target-scoped environment command/file sources before legacy fallbacks. Save operations replace only their owned SDN section and retain siblings. Deployment warnings classify only the parsed hostname. Redaction masks sensitive headers, URL credentials/query parameters, and assignment forms before output.
