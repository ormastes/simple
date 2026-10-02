# POP3 and saved mail credentials

User selected saved passwords using Simple's existing encrypted storage on
2026-09-29: "ok add todo to increase security. go on". Native-store/AEAD
hardening is separately tracked in credential_storage_hardening_2026-09-29.md.
Interpret rejected/expired credentials as the recovery trigger; Git push and
PR merge are authorized. Background mail notifications are outside this change.

- REQ-001: Configure POP3 over TLS, list messages and retrieve without deletion.
  Keep SMTP sending and existing IMAP functionality. Reject unsupported POP3
  flags/folders/search/mutations explicitly. IDs are POP3 session message numbers.
- REQ-002: Encrypt newly saved passwords using the Simple credential store.
  A compiled helper receives secrets via stdin, never argv. Fail closed when
  unavailable; no new plaintext persistence. Legacy plaintext remains readable.
- REQ-003: On authentication rejection only, prompt privately on a controlling
  terminal and retry once. Save only a successfully authenticated replacement.
  Noninteractive commands return an actionable error instead of hanging.
- REQ-004: Explicit password sources override saved credentials. Support a
  password command and password input file; never print the supplied secret.
- REQ-005: Dev-hub routes POP3 through mail-cli and forwards credential options;
  terminal prompts bypass captured stdout. Both clients share mail-cli config.
- REQ-006: No retry of ambiguous SMTP timeout/send/receive failures, no automatic
  mail deletion, no plaintext fallback if encryption fails.
- REQ-007: User additionally requires configurable mail config file/directory
  and a shared dev-hub account file. Dev-hub and mail-cli read one shared SDN file through the canonical
  parser and forward the identical location. Legacy JSON requires an explicit
  file selection; import is separately opt-in. An explicit DevHub SDN path
  selects only its `email` section, containing the same default/account schema.
  Other provider sections are ignored; missing or invalid email settings fail
  without merging defaults or falling back to another file. Standalone
  `email.sdn` remains supported. Combined documents are read-only in mail-cli's
  settings writer so unrelated sections cannot be overwritten.
- REQ-008: Run the shared client on Windows/Linux/macOS/BSD with documented
  host dependencies and a Windows launcher. Native Simple helper builds and
  actual host execution must be separately verified; no implied cross-host PASS.
- REQ-009: Expand a leading literal `{home}` in supported path inputs without
  invoking shell evaluation, and use quoted placeholders in launch examples.

No production merge without required verification. A blocked runtime is reported
honestly; it does not authorize a seed fallback or fabricated test evidence.
