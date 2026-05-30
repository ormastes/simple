# Windows hardening SPipe/local install step - 2026-05-30

## Scope

SPipe submodule setup, local package checks, and `/sp_dev` command wiring on
Windows.

## Changes

- Added `scripts/setup-spipe-submodule.ps1` as the native Windows wrapper for
  initializing `.spipe/spipe` and running the submodule link setup.
- Added `scripts/install-spipe-dev-command.ps1` as the native Windows checker
  for `/sp_dev` wiring.
- Updated `.codex/skills/sp_dev/SKILL.md` to document the Windows check
  command.

## Evidence

- `git submodule update --init --recursive -- .spipe/spipe` checked out
  `.spipe/spipe` at `ee79ffb714474baf6699e9a0f7d99421ef40f00f`.
- `powershell -ExecutionPolicy Bypass -File scripts\setup-spipe-submodule.ps1`
  completed. Existing host entries were skipped when already present.
- `powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
  returned `STATUS: PASS spipe-dev-command wiring`.
- From `.spipe/spipe`, `npm run check` passed `node --check` for
  `cli/spipe.js` and `mcp/server.js`.
- `node cli\spipe.js info` printed the expected SPipe module path and process
  surfaces.

## Windows local-link note

The host had existing file-style symlinks for `doc\00_llm_process\...` entries.
PowerShell could inspect them, but Node reported the targets as missing. Running
`scripts\setup-spipe-submodule.ps1 -Force` locally replaced them with Windows
junctions and `node cli\spipe.js doctor C:\Users\ormas\dev\simple` then reported
`target_link` for all six surfaces and `spipe_doctor=pass`.

Those junction replacements are local install state and are not committed,
because the repository stores portable link entries. Re-run the PowerShell setup
with `-Force` on Windows if Node-based SPipe tools report `target_missing`.
