# Mail-cli: POP3 and saved passwords

See [platform setup](../../../tools/mail-cli/README.md) for Linux/macOS/BSD
dependencies and the Windows Git Bash launcher. Windows support requires those
dependencies and a native credential-helper build; Linux tests do not certify
Windows, macOS, or BSD runtime behavior.

Use `mail auth login --protocol pop3 --account work` to configure a TLS POP3
maildrop plus SMTP sending. POP3 defaults to port 995. Mandatory STLS is
available through the `starttls` setting; certificate checks remain enabled.

`mail inbox --account work --json --limit 25` lists messages. `mail read 1
--account work` retrieves message number 1 without deleting it. Message numbers
may change between sessions. POP3 does not support mail-cli folders, search,
flags, archive, delete, move or drafts. Reply/forward reuse message retrieval
and SMTP. Inbox header display retrieves whole messages, capped at 16 MiB each.

## Password storage

Install an admitted, compiled `src/app/mail_credentials/main.spl` artifact as
`simple-mail-credentials`, or point `MAIL_CREDENTIAL_BIN` to it. The client
does not compile it on startup and does not use a Rust bootstrap seed. Until
that artifact is available, encrypted saves fail explicitly. Existing external
password commands remain usable.

New saved passwords use Simple's `encrypted:v2:` format and the existing
`{home}/.simple/credential_key`. The key itself is stored locally, and CBC records
lack an authentication tag. This is not an OS credential vault; see the
[hardening TODO](../../08_tracking/todo/credential_storage_hardening_2026-09-29.md).
Existing plaintext account records remain readable; `auth password` rewrites
the selected password in encrypted form after successful authentication.

`mail auth password --account work --password-file /private/password.txt`
validates and saves a replacement. Without an explicit source it prompts on
the controlling terminal with echo disabled. Protect password input files and
remove them when no longer needed. `--password-cmd 'pass show mail/work'`
uses a password manager instead. Never put a literal password in that command.

For normal operations, `--password-file` or `--password-cmd` overrides the saved
credential without persisting it. Rejected saved credentials prompt once; a
successful replacement is encrypted and saved. `--non-interactive` forbids
prompts. Passwords do not appear in curl argv or normal diagnostic output.
An unavailable helper never causes plaintext fallback.

If credential initialization was interrupted, the client fails closed while
`{home}/.simple/mail-credential.lock` exists. Confirm no writer remains before
removing that empty lock directory. Never delete the credential key to fix a
login error: doing so makes existing encrypted credentials unreadable.

## Dev-hub

New dev-hub accounts use **one shared SDN file** at
`{home}/.config/devhub/email.sdn`. Run `devhub email auth login --protocol pop3
--account work` to configure it. Dev-hub parses account metadata from that file
and passes `--config-file` with the same path to mail-cli. Password resolution
and updates happen in mail-cli; dev-hub does not duplicate saved passwords.

Use `mail inbox --config-file "{home}/.config/devhub/email.sdn" --account work` for
direct access to that same account. Both clients also accept `--config-dir DIR`
to select `DIR/email.sdn`, or `--config-file FILE` for an explicit SDN file.
Explicit legacy JSON files remain readable. For example,
`devhub email inbox --config-file /private/team-mail.sdn` reads
that file and forwards its exact location. Conflicting file/directory flags
are rejected. Mail-cli alone supports matching MAIL_CONFIG_FILE/DIR environment
defaults. Custom file parents are created when configuration is initialized.

The shared schema has `default_account` and `accounts` blocks; account fields
include `protocol`, `email`, `username`, `pop3_server`, `pop3_port`,
`smtp_server`, `smtp_port`, `tls`, and `password` (encrypted) or `password_cmd`.
IMAP accounts use `imap_server`/`imap_port`. A Graph account specifies
`protocol: graph` and its Graph identity fields; its authentication remains
separate. Do not forward Graph accounts to direct mail-cli operations.

When `email.sdn` is absent, DevHub can still read its former `email.json`.
mail-cli imports that file, or its older `~/.config/mail-cli/config.json`,
into `email.sdn` on first configuration initialization. The source JSON file
is left untouched for review.

`devhub email auth password --account work --password-file /private/password.txt`
updates the shared file after validation. Credential flags also work on other
mail-cli backends. On Windows, set `DEVHUB_MAIL_BIN` to the Git Bash executable
and `DEVHUB_MAIL_SCRIPT` to the mail script using forward-slash paths; this avoids
depending on shebang or command-file associations in native process launching.

Dev-hub allows up to five minutes for interactive mail commands, including
password entry; `--non-interactive` retains a thirty-second subprocess bound.
Account setup (`auth login`) inherits the terminal so all prompts are visible;
it is explicitly interactive and is not subject to that capture timeout.

Path arguments accept a leading literal `{home}`. Quote it even in launch
examples, such as `devhub email inbox --config-file "{home}/.config/devhub/email.sdn"`.
The application expands it from the host home-directory environment; neither
Bash nor PowerShell needs to interpret the placeholder.
