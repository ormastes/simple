# Windows environment snapshots omit explicitly empty values

P2. Fix implemented; full bootstrap verification pending.

`rt_env_set` deliberately preserves an empty Win32 value after `_wputenv_s`
removes the corresponding CRT entry. `rt_env_get` reads that Win32 value, but
`rt_env_vars` enumerated `_environ`, so a snapshot omitted the variable. Direct
`SetEnvironmentVariableW` writes were also absent from snapshots. This is
separate from the Simple wrapper's tuple-layout normalization.

The Windows branch now snapshots `GetEnvironmentStringsW`, converts names and
values with the existing strict UTF-8 helper, and releases the OS block with
`FreeEnvironmentStringsW`. It keeps empty values, splits at the first equals
sign, excludes hidden drive entries beginning with `=`, and retains the existing
array-of-two-tuples ABI. The POSIX branch is unchanged. Failed acquisition or
conversion returns nil and releases constructed results rather than returning
a partial snapshot. The OS block's lifetime and read-only contract follow
[Microsoft's API documentation](https://learn.microsoft.com/windows/win32/api/processenv/nf-processenv-getenvironmentstringsw).

## Executed Windows evidence

Base source: `6d496f82c5acabc2fc52b2b78146272e664dc371`. LLVM clang 23.1.2,
x86_64-pc-windows-msvc, MSVC 14.44.35207, Windows SDK 10.0.26100.0, owner1.
The real 42-object C runtime composition was used; only `runtime_native.c`
was replaced for the candidate. No product owner was stubbed.

- Before: the real environment regression exited 1 with four failures among
  20 parent checks: empty value, Win32-only write, and old/new snapshots of that
  variable. ASCII/UTF-8, equals, removal, and the hidden-drive child passed.
- After: the same behavior checks exited 0, 20/20 passed. The spawned child
  additionally checks its real hidden-drive environment block and public view.
- Separate failure-path run: 8/8 passed. An injected failed OS acquisition
  returns nil and frees the result container. A real malformed UTF-16 value
  returns nil, frees the acquired OS block, and restores the heap-registry count
  after discarding partial tuples and strings.

Regression sources:
`src/runtime/test/rt_windows_env_snapshot_selfcheck.c` and
`src/runtime/test/rt_windows_env_snapshot_faults.h`. The forced header affects
only the failure-test runtime object; its successful calls delegate to the
actual Windows APIs. Retained logs and binaries are under
`C:/dev/wt/g100-win-env-snapshot/build/env-snapshot-evidence/`.

The original native Simple normalization probe initially reported
`writes=1 ascii_matches=1 utf8_matches=1 empty_matches=0` in the `cli_native`
lane. Rebuilding that retained GNU runtime object, rerunning the normalized
Simple probe, and qualifying the complete bootstrap/test runner remain separate
integration gates. The C results above do not admit a compiler generation.
