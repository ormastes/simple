# Windows Codex console popup workaround

## Scope and cause

This is host CLI setup, not a SPipe plugin, MCP server, or Git hook.
On the affected Windows host, Codex 0.158.0's managed app-server directly
launched `git rev-parse HEAD`, `git remote -v`, and `git status --porcelain`
with `core.hooksPath=NUL`. Those commands collect repository context even
during ordinary chat. The user confirmed that explicit `--no-daemon` stops
the observed popups. `daemon_auto_start = false` was loaded but did not
give the same result on that host. The exact reason for that difference
has not been established.

Related upstream report: https://github.com/openai/codex/issues/48422

## Install on each Windows host

Requires Node.js and the npm installation of `@openai/codex` supporting
`--no-daemon`. From the repository, run in PowerShell:

```powershell
./scripts/setup/install-windows-codex-launcher.ps1
```

The installer creates `%LOCALAPPDATA%\Simple\codex-cli` and prepends it to
the user PATH. It does not copy credentials or modify MCP, SPipe, Git hooks,
execution policy, or npm-generated launchers. It does not stop active work.
It uses the installed npm package, so npm updates do not overwrite the wrapper.
If npm's installation prefix moves, rerun the installer.

Open a new terminal (restart the terminal application if its PATH is stale).
Check `where.exe codex` in CMD, or `Get-Command codex -All` in PowerShell.
The new directory must precede other Codex launchers. System PATH entries
and PowerShell functions/aliases may take precedence; invoke the installed
`codex.cmd` by its full path if necessary. A prior PowerShell `codex` function
must be removed from that host's profile to use this wrapper by name.

Plain `codex`, `codex resume`, and `codex fork` add `--no-daemon` automatically.
An explicit `--no-daemon` is not duplicated. Direct `agents`, `app-server`,
`remote-control`, and `--remote` invocations retain server behavior. Put those
subcommands first; for other server-specific argument arrangements, invoke
the original npm launcher explicitly. Both PowerShell and CMD preserve
arguments, standard streams, and the child exit code.

This bypasses the affected daemon path; it is not an upstream process-launch
fix and does not cover the Codex desktop app or IDE extension.

## Remove

Remove `%LOCALAPPDATA%\Simple\codex-cli` from the user PATH using Windows
Environment Variables settings, then open a new terminal. The original npm
installation remains available. Delete the wrapper directory if desired.
