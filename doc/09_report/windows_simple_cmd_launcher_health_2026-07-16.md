# Windows simple.cmd Launcher Health - 2026-07-16

Current Windows PowerShell run:

```powershell
$env:SIMPLE_WIN32_MDI_PROOF_PATH='build/tmp/bin_simple_cmd_source_probe.env'
$env:SIMPLE_WIN32_MDI_HOLD_MS='100'
bin\simple.cmd src\os\hosted\hosted_win32_mdi_probe.spl --interpret
bin\simple.cmd --version
```

Result:

- `source_launch_exit=0`
- `proof_exists=True`
- `version_exit=0`
- `version=Simple v0.9.6`
- `status=pass`
- `backend=win32-native`
- `window_title=SimpleOS Win32 Hosted MDI Probe`
- `drag_moved=true`
- `focus_cycle_changed=true`
- `rendered_titlebar_css_applied=true`
- `rendered_titlebar_css_pixels=6784`

Code change:

- `bin/simple.cmd` now ignores zero-byte runtime candidates.
- `.spl` source-file launches prefer the current built Rust driver at
  `src/compiler_rust/target/debug/simple.exe` when present, because the stale
  April Windows release binary reports current source paths as missing.
- Non-source commands such as `--version` still use the release candidate path.

This is launcher health evidence, not a pure-Simple release-binary completion
claim. The current driver prints the bootstrap-seed warning; the launcher
fallback exists so Windows-hosted source evidence can run until a fresh
pure-Simple release binary replaces the stale release candidate.
