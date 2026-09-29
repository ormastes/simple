Changed files:

- [Producer](scripts/setup/materialize-symlinks-windows.shs): strict receipt validation, held policy snapshot, consumer revalidation flag.
- [Tests](test/01_unit/scripts/materialize_symlinks_windows_test.shs): malformed receipts and policy race fixtures.
- [Contract/bug doc](doc/08_tracking/bug/windows_materialized_symlink_alias_git_state_timeout_2026-09-09.md): exact v2 contract and mandatory pending revalidation.

Exact attempted command:

```powershell
& 'C:/dev/tool/msys2/usr/bin/sh.exe' -c '. ./scripts/setup/host-env.shs && host_env_apply_path && mkdir -p /c/Users/ormas/AppData/Local/Temp/simple-materialize-root-canonical && export TMPDIR=/c/Users/ormas/AppData/Local/Temp/simple-materialize-root-canonical && /usr/bin/sh test/01_unit/scripts/materialize_symlinks_windows_test.shs'
```

**Exit 1:** temporary-root creation failed with `Permission denied`. The test never started. Stopped without retrying.

Remaining risks: changes are runtime-unverified; pending absence requires consumer revalidation immediately before use. Unrelated concurrent work was preserved.