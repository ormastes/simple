Changed only:

- `scripts/setup/materialize-symlinks-windows.shs`
- `test/01_unit/scripts/materialize_symlinks_windows_test.shs`

Added numeric tag/handle identity validation, typed diagnostics, argument-safe creation, byte-exact blob checks, complete digest validation, HEAD-bound classification, protected atomic publication, and behavioral fixtures.

Ran once:
`C:\msys64\usr\bin\sh.exe test/01_unit/scripts/materialize_symlinks_windows_test.shs`

**Exit 1 — environmental blocker:** setup line 12 failed: `mktemp … /tmp/simple-materialize-links.XXXXXX: Permission denied`.

Stopped immediately. No patch/rerun, broader tests, or repository commits. Windows API behavior and fixtures remain unverified; Part 1 is not PASS.