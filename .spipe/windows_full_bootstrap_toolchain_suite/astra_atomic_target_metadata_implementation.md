Changed only:

- [Producer](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs): held-handle metadata capture, reparse/replacement rejection.
- [Focused test](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs): exact decoded-row assertions, independent oracle, replacement fixture, records-only fault hooks.

**Design:** schema v2 uses UTF-8 `\\?\C:\…` final paths; the consumer contract is documented inline. Directories use SHA `-`. The four-entry allowlist remains unchanged.

**Single test command** (PowerShell, with `MATERIALIZER_TASK_TMP` set to the fresh task directory):

```powershell
& 'C:/dev/tool/msys2/usr/bin/sh.exe' -c '. ./scripts/setup/host-env.shs; host_env_apply_path; export TMPDIR=$(cygpath -u "$MATERIALIZER_TASK_TMP"); sh test/01_unit/scripts/materialize_symlinks_windows_test.shs'
```

TMPDIR: `.spipe/windows_full_bootstrap_toolchain_suite/metadata-once-20260910-7828dc3d4a3f440c8db47a8f05aa66b2`

**Exit code: 1. Exact failure:**

```text
mkdir: cannot create directory ‘/c/Users/ormas’: Permission denied
FIRST FAILURE: case=positive line=21 command=mkdir -p "$repo" exit=1
```

Stopped without rerunning. Fixture setup failed before producer execution, so native behavior and race assertions remain unverified. Consumers require explicit v2 support. Unrelated changes were preserved; no consumer/bootstrap/docs edits, actual-tree invocation, or Git publication operations occurred.