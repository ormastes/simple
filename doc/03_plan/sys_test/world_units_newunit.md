<!-- codex-impl -->
# World Units and Newunit System Test Plan

- REQ-WUN-001/002: parser tests prove `newunit UserId: i64 as uid` succeeds and measurement-family or derived `newunit` forms fail.
- REQ-WUN-003/004: catalog consistency tests inspect SDN entries and `ExactRatio` helpers for exact derived factors.
- REQ-WUN-005/006: catalog tests assert distinct year variants and ISO 4217 currency identity for `USD`.
- REQ-WUN-007: primitive API lint samples use `newunit` or measurement `unit` instead of raw public primitives.
- NFR-WUN-003: SFFI lint coverage verifies ABI-compatible named wrappers pass and unsupported wrappers fail.
