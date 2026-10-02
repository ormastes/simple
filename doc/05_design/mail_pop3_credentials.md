# Mail POP3 and credential flow

## Configuration and invocation

Accounts retain IMAP defaults when `protocol` is absent. POP3 accounts set
`protocol: pop3`, `pop3_server`, `pop3_port`, and `tls` (implicit or starttls).
SMTP settings remain per account. Dev-hub uses `provider: pop3` and the same
account name in its email config. No password is duplicated in dev-hub config.

`--config-file` selects either standalone email.sdn or a combined DevHub file.
The latter uses `email:`, with indented `default_account:` and `accounts:`
children. Both consumers select this subtree through parse_email_sdn_json;
no sibling provider settings enter the mail projection. The selected path is
passed unchanged to the shell client. Canonical SDN issues inside the selected
subtree are rejected with redacted MAIL_CONFIG_* codes. Account values are
projected using the canonical JSON dictionary constructor.

The projection carries internal `_mail_config_scope` metadata. Combined-file
reads are supported; mail settings/password persistence fails explicitly with
MAIL_CONFIG_EMAIL_READ_ONLY before its legacy block writer can change other
sections. Standalone email.sdn remains writable. A user can supply a transient
password-file/command override without modifying a combined document.

Password precedence is explicit password file, explicit password command,
saved password command, then saved encrypted/legacy password. New password
saves always use Simple encryption. Supplying both explicit sources is an
argument error. Empty/multiline passwords are rejected before transport.

The helper uses the existing key, or initializes one from CSPRNG material
under a directory lock. Key deletion/rotation is never automatic. Its stdin
contains one secret line; stdout contains the transformed result only.

## Recovery

1. Curl exit 67, an identified account, and no explicit override permit one
   private terminal prompt. TLS and transport failures do not prompt.
2. Retry the same operation once using the replacement. SMTP exit 67 precedes
   accepted message submission; timeout/send/receive failures are not retried.
3. On success encrypt and atomically save the replacement, removing a superseded
   saved password command. On failure/cancellation retain prior config.
4. If delivery succeeded but saving failed, report the save failure separately
   while retaining successful delivery status, preventing caller-driven resend.
5. `auth password` explicitly validates a replacement with incoming NOOP before
   persistence. Noninteractive recovery returns actionable error text.

## Verification

Modern SSpec scenarios wrap actual offline client execution, with step labels
and assertions on parsed results, exit codes and transport recordings.
Separate real-store scenarios must establish encryption/decryption and key
behavior. Fake-helper tests cannot satisfy that acceptance criterion.
Dev-hub routing and credential forwarding require focused SSpec execution.
Full acceptance also needs helper build/deployment and runtime identity evidence.
