# Mail POP3 acceptance plan

| Requirement | Required evidence |
|---|---|
| REQ-001 | Offline POP3 listing/read over TLS; JSON result; no IMAP/DELE; unsupported verb failure |
| REQ-002 | Real Simple helper round trip and private key file; orchestration fake-helper persistence separately |
| REQ-003 | Rejected login one retry; successful replacement saved; failed/cancelled replacement preserved |
| REQ-004 | File/command precedence, conflict/empty input errors, no password in transport argv |
| REQ-005 | Dev-hub POP3 provider routing, credential-option forwarding, unsupported action errors |
| REQ-006 | SMTP timeout no retry, encryption failure no plaintext fallback, existing IMAP regression probe |
| REQ-007 | Shared file/directory selection, update isolation, JSON parse -> exact config argv |
| REQ-008 | Windows launcher fixture; macOS-compatible attachment encoding; native OS runtime matrix |
| REQ-009 | Literal home-prefix expansion for config, password input, helper path and dev-hub script prefix |

Run each acceptance check once per unchanged revision. At most three repair
cycles. Tests use synthetic credentials and isolated temporary config roots.
Do not connect to the user's real mailbox or send messages during verification.
Record missing native runtime or deployment as TEST_BLOCKED, never PASS.
