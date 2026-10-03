# Confluence access repair

Scope: user-authorized DevHub Confluence access fixes, with named-target credential isolation confirmed by the coordinating agent. Existing Cloud/DC v1 content routing and gateway prefixes remain the contract.

| Requirement | Acceptance |
| --- | --- |
| REQ-CONFLUENCE-ACCESS-001 | Preserve Cloud `/wiki`, Data Center context paths and complete gateway prefixes; absent URL stays absent. |
| REQ-CONFLUENCE-ACCESS-002 | Quote both CQL title and space literals, escaping backslashes before quotation marks. |
| REQ-CONFLUENCE-ACCESS-003 | Return decoded JSON strings; malformed listing shapes fail instead of reporting an empty successful page. |
| REQ-CONFLUENCE-ACCESS-004 | Redact transport and HTTP error diagnostics while preserving successful content and HTTP status; never automatically replay writes. |
| REQ-CONFLUENCE-ACCESS-005 | Resolve environment, command and file credentials inside the selected target; missing named credentials never borrow default credentials. Legacy unnamed credentials remain supported. |

Canonical executable acceptance: `test/03_system/app/devhub/feature/confluence_access_spec.spl`.
