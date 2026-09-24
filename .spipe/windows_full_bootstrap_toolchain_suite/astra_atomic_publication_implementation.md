Changed only:

- [Producer](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs): identity reacquisition, native placeholder deletion, atomic directory creation, strict metadata parsing.
- [Tests](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs): publication swaps, malformed metadata, all four policy rows and near-matches, six decoded fixture associations.

Exact test command, run once:

```powershell
& 'C:/dev/tool/msys2/usr/bin/sh.exe' -c '. ./scripts/setup/host-env.shs; host_env_apply_path; export TMPDIR=/c/dev/tool/msys2/tmp; /usr/bin/sh test/01_unit/scripts/materialize_symlinks_windows_test.shs'
```

**Exit code: 1.** Setup failed with permission denied creating the temporary directory. Stopped immediately; no rerun or actual-tree producer invocation.

**Incomplete:** changes remain unverified. Pending-path absence still has a check-to-publication race; not all atomic blockers are closed. Unrelated dirty work was preserved.