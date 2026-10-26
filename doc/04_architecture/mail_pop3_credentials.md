# Mail protocol and credential boundaries

The existing shell mail-cli remains the protocol/UI owner. Its shared curl
boundary supplies credentials through curl's config stdin, disables curlrc,
and owns bounded authentication recovery. Protocol-specific code never owns
cryptography. Dev-hub invokes the same mail-cli account and credential paths.
Its default shared account file is `~/.config/devhub/email.json`; an explicit
file or directory selector overrides it and is passed to mail-cli. JSON is
the shared schema, while legacy `email.sdn` retains the previous separate route.
`email_support.spl` owns parsing, credential options and subprocess arguments;
`cmd_email.spl` owns command dispatch. The command module exports the support
surface for existing callers. An optional DEVHUB_MAIL_SCRIPT argv prefix lets
native Windows processes invoke Bash without app-level OS branches.

POP3 is a separate read-only adapter for list/retrieve. The existing MIME
formatter and SMTP sender remain shared. POP3 command dispatch rejects IMAP
semantics (flags, folders, search, drafts and mutations). Message numbers are
explicitly session-local, not durable UIDs. No DELE is issued by retrieval.

`src/app/mail_credentials/main.spl` is a compiled, narrow stdin/stdout bridge to
the existing Simple terminal credential store. Only encrypt/decrypt are public
operations. The bridge cannot select plaintext storage. The shell serializes
key initialization and atomically replaces account config only after success.
The existing key/cipher security limitations are tracked separately in
`doc/08_tracking/todo/credential_storage_hardening_2026-09-29.md`.

Runtime compilation and seed fallback are prohibited. Deployment must provide
the compiled helper via PATH or MAIL_CREDENTIAL_BIN. Its absence is a real
error, not permission to save plaintext. A fake helper proves orchestration
only, never encryption correctness or deployability.

Dev-hub keeps secrets out of subprocess argv by forwarding only a password-file
path or password-manager command. Prompts go directly to the controlling
terminal, not captured JSON output. Noninteractive mode forbids prompts.
Interactive subprocess timeout is bounded at five minutes; noninteractive
mode retains thirty seconds. Curl requests remain individually bounded.
Explicit interactive account setup inherits terminal streams and is exempt
from the capture timeout. Noninteractive setup fails before asking for input.

Startup adds no source-tree scans or runtime rebuilds. Inbox fetches at most
the selected limit (1..1000, default 25); POP3 header display currently retrieves
whole messages with a 16 MiB per-message transport limit. No persistent mailbox
cache exists in this change. Credential state is reloaded after replacement;
no password is retained in a cross-command cache.
