# DevHub multi-target gateway requirements

The user selected the following requirements on 2026-09-14.

- REQ-001: Confluence supports multiple named targets selected by `--host` or `--profile`.
- REQ-002: The configured default target wins; otherwise the first named target is the default.
- REQ-003: Each target carries ordered, repeated arbitrary HTTP headers.
- REQ-004: Each target may define a complete `gateway_url`; routing stays in `config.sdn` and secrets stay in `auth.sdn`.
- REQ-005: DevHub API automatically attaches the selected target's configured headers only when routing through its gateway; explicit same-name CLI headers override them case-insensitively.
- REQ-006: Auth status warns when URL shape and deployment disagree and supports `--quiet`/`--silent`.
- REQ-007: Verbose diagnostics redact credentials and sensitive `token|key|secret|password` assignments using either `:` or `=`.
- REQ-008: Config and credential updates preserve sibling named targets and unknown credential sections.
