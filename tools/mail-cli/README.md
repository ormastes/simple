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
bash tools/mail-cli/bin/mail auth status --config-file "{home}/.config/devhub/email.json"
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
& .\tools\mail-cli\bin\mail.cmd auth status --config-file '{home}/.config/devhub/email.json'
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

dev-hub passes its selected JSON configuration with `--config-file`. Both tools
also accept `--config-dir DIR` for `DIR/config.json`. For direct process
execution on Windows, configure `DEVHUB_MAIL_BIN` to the Git Bash executable and
`DEVHUB_MAIL_SCRIPT` to the absolute, forward-slash path of `bin/mail`; the
script becomes the first argument. Ensure Git's Unix utilities are on the
inherited PATH. On Unix, the executable `bin/mail` can run directly.

Never place passwords in command lines or launcher files. See the
[mail-cli guide](../../doc/07_guide/app/mail_cli.md) for configuration and
password input modes.
