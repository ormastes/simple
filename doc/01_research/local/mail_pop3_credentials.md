# Mail POP3 and credential recovery: local research

Status: researched; selections recorded in the final requirements. Date: 2026-09-29.

Scope: `tools/mail-cli`, `src/app/devhub/cmd_email.spl`, focused tests.
Isolated branch: `codex/mail-pop3-credentials-20260929`, based on local
`origin/main` at `240d9509bd4`. The shared workspace has unrelated changes;
none were copied into this lane.

Findings:

- `tools/mail-cli/bin/mail` sources shell libraries and requires curl IMAP
  support globally. POP3-only use needs protocol-aware dependency checks.
- `lib/config.shs` resolves account fields and plaintext passwords, or executes
  `password_cmd`. Config files have mode 0600, but contain recoverable plaintext.
- `lib/auth.shs` prompts for IMAP/SMTP endpoints, tests IMAP NOOP, and stores a
  password or password command. Status duplicates password-resolution logic.
- `lib/imap.shs` exposes folder, SEARCH, header, body, and mutation primitives.
  POP3 must not be passed into these IMAP operations silently.
- `src/app/devhub/cmd_email.spl` routes gmail/outlook_imap to mail-cli through
  `process_run_bounded`, with a 30-second timeout and captured output.
  Interactive recovery needs terminal-aware ownership rather than a prompt
  hidden in captured stdout. The Graph backend is separate.
- Existing offline coverage lives in
  `test/01_unit/tools/mail_cli/mail_cli_spec.spl` and its shell probe, plus
  `test/01_unit/app/devhub/email_cmd_spec.spl` and related facade specs.
- No `secret-tool`, `pass`, or `security` executable was found on the current
  host PATH. A manager-backed implementation must report unavailability and
  must not fall back to plaintext storage.

User subsequently chose saved credentials using the existing Simple encryption
with an explicit security-hardening TODO, then requested shared configurable
dev-hub/mail-cli storage, modern SSpec, and Windows/Linux/other-host support.
Rejected/expired credential recovery and Git PR publication are the adopted scope.

Implementation should preserve the existing tool boundary; a wholesale
replacement of the shell mail client requires separate scope justification.
Do not access real saved credentials or contact real mail accounts in tests.
