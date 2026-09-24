Changed only:

- `scripts/setup/materialize-symlinks-windows.shs`: two-phase ancestor validation/creation with retained no-follow handles; publication and cleanup unchanged.
- `test/01_unit/scripts/materialize_symlinks_windows_test.shs`: added the absence precondition immediately before invocation; retained the postcondition.

Ran exactly once:
`C:/dev/tool/msys2/usr/bin/sh.exe test/01_unit/scripts/materialize_symlinks_windows_test.shs`

Environment:
`TMPDIR=C:/Users/ormas/dev/simple/.spipe/windows_full_bootstrap_toolchain_suite/receipt-ancestor-once-a10ecfa3a5fb4b988340ffa627e924e7`

**Exit 1**, first failure:
`FIRST FAILURE: case=positive line=21 command=mkdir -p "$repo" exit=1`
Diagnostic: `mkdir: cannot create directory ‘/c/Users/ormas’: Permission denied`

Stopped immediately without patching or rerunning. Remaining risk: fixture setup failed before producer execution, so the correction remains unverified. Unrelated dirty files were preserved.