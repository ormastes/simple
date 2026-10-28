# mail-cli platform setup

The client runs under Bash with curl, jq, base64, and standard Unix utilities.
Use a curl build with the protocols you need: POP3/POP3S or IMAP/IMAPS, plus
SMTP/SMTPS for sending. Install a compiled `simple-mail-credentials` helper for
your OS/architecture and set `MAIL_CREDENTIAL_BIN` to its executable path.
The client refuses encrypted password operations when that helper is missing.

## Linux, macOS, and BSD

Install Bash, curl, and jq with your platform package manager. Put
`tools/mail-cli/bin` on PATH, or invoke `bash tools/mail-cli/bin/mail` directly.
The implementation uses the platform's base64 and date utilities; GNU and BSD
date forms are supported. Perl is optional for quoted-printable decoding.

```bash
export MAIL_CREDENTIAL_BIN="{home}/.local/bin/simple-mail-credentials"
bash tools/mail-cli/bin/mail auth status --config-file "{home}/.config/devhub/email.sdn"
```

Use a private configuration directory. `TMPDIR` selects temporary-file storage.
macOS and BSD runtime tests still need to be run on those systems; Linux results
are not evidence that their native crypto/helper implementations work.

## Windows

Install Git for Windows (Git Bash), jq, and a suitable curl build, and expose
them on the Git Bash PATH. Use `tools\mail-cli\bin\mail.cmd` from cmd.exe or
PowerShell. The launcher detects common Git installations; `MAIL_BASH` can name
a different Git Bash executable. It deliberately does not discover `bash.exe`
on PATH, where that name can select WSL and a different filesystem/configuration.

```powershell
$env:MAIL_BASH = 'C:\Program Files\Git\bin\bash.exe'
$env:MAIL_CREDENTIAL_BIN = '{home}/bin/simple-mail-credentials.exe'
& .\tools\mail-cli\bin\mail.cmd auth status --config-file '{home}/.config/devhub/email.sdn'
```

Use forward slashes in paths passed to Bash, including configuration and helper
paths. Keep the credential key and configuration in directories protected by
your Windows account's ACL: Unix chmod alone does not establish Windows ACLs.
The native helper and Bash must agree on HOME and the credential key location.
Windows execution and the native helper require testing on Windows before a
Windows release is declared verified.

The client expands a leading `{home}` in config-file, config-directory,
password-file and helper-executable paths; quote these arguments. This is
application expansion, not shell evaluation. Dev-hub supports the same prefix
in config selectors and its executable/script overrides. Do not put `{home}`
directly in the shell's executable position: start the installed command (or a
repo-relative launcher) and supply the placeholder as an argument.

## dev-hub invocation

Both clients read `email.sdn` through the canonical Simple SDN parser. Install
the rebuilt `simple-mail-credentials` helper with its `config-json PATH` mode;
the shell client does not compile source or fall back to an AWK parser.
`MAIL_CONFIG_BIN` can select that helper independently of `MAIL_CREDENTIAL_BIN`.
The bridge emits account metadata, credential commands and encrypted envelopes,
so do not capture its output in public logs. It rejects plaintext `password`
values, duplicate keys, invalid field types and malformed port/TLS settings
with stable `MAIL_CONFIG_*` diagnostics that contain no input values.
Use `password_cmd` for a credential reference or the existing encrypted password
store. Explicit `.json` paths retain legacy compatibility; SDN parsing never
silently falls back to JSON. One-time JSON import requires
`MAIL_IMPORT_LEGACY=1` and rejects plaintext credentials. Account selection is `--account` then
`default_account`; credential overrides retain `--password-file` then
`--password-cmd` precedence. An unknown selected account never uses a sibling.
POP3 defaults to port 995 for implicit TLS and port 110 for STARTTLS.

dev-hub passes its selected SDN configuration with `--config-file`. Both tools
also accept `--config-dir DIR` for `DIR/email.sdn`. For direct process
execution on Windows, configure `DEVHUB_MAIL_BIN` to the Git Bash executable and
`DEVHUB_MAIL_SCRIPT` to the absolute, forward-slash path of `bin/mail`; the
script becomes the first argument. Ensure Git's Unix utilities are on the
inherited PATH. On Unix, the executable `bin/mail` can run directly.

Never place passwords in command lines or launcher files. See the
[mail-cli guide](../../doc/07_guide/app/mail_cli.md) for configuration and
password input modes.

## Hosted fixture dependency

The host-fixture credential executable deliberately implements only synthetic
encryption orchestration. SDN scenarios require a separate, real
`MAIL_CONFIG_BIN`; that executable must run the canonical Simple parser.
`scripts/ci/prepare_mail_config_helper.py` builds the current helper source with
an existing, pinned Phase-2 compiler and exercises valid and malformed SDN
before exporting its path to subsequent workflow steps. It never rebuilds the
compiler or falls back to a seed, another parser, or skipped assertions.

Configure the repository variable `MAIL_CI_PHASE2_PRODUCERS_JSON` with qualified
producer bundles for the hosted platforms, for example:

```json
{
  "linux-x86_64": {
    "phase": 2,
    "url": "https://example.invalid/existing-qualified-phase2.tar.gz",
    "sha256": "<exact 64-character lowercase bundle SHA-256>",
    "format": "tar.gz",
    "compiler": "bin/simple",
    "asset_root": "."
  }
}
```

Supported host keys are `linux-x86_64`, `darwin-arm64`, `darwin-x86_64` and
`windows-x86_64`. Formats are `file`, `tar.gz` and `zip`; bundles must include
the producer's runtime dependencies and an available native toolchain. The
digest pins the complete bundle, while the producer generation comes from its
qualification record. A missing profile, checksum mismatch or failed real
helper build remains an infrastructure failure. The workflow preserves build
logs and producer/helper digests instead of reporting the SDN scenarios passed.

TODO (hosted CI infrastructure, 2026-10-27): provide qualified existing Phase-2
producer profiles for every matrix host and qualify the resulting current-source
helper builds. No Linux/Darwin profile has been selected. The provisioning
admission tests passed locally; the focused config and placeholder fixtures
passed with the existing real Windows SDN helper. This is not hosted-matrix or
new-helper-build acceptance, and the workflow remains blocked until those
external producer dependencies are provisioned.
