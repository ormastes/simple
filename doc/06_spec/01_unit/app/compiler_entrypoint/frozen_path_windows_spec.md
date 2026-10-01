# Windows verbatim frozen source path mapping

Executable: `test/01_unit/app/compiler_entrypoint/frozen_path_windows_spec.spl`.
Scope: seven-plan item 1, explicit Windows host row.
This is a manually maintained scenario companion; production docgen is pending.

Confirm a real source exists through its `\\?\C:\...` spelling, then call
the public frozen-path owner and compare its exact admitted snapshot identity.
There is no substitute success on non-Windows hosts.

Run this file explicitly **on Windows**. `# @platform: windows` is recognized
by the manifest scanner, and ordinary interpreter/native/SMF directory discovery
excludes it on every host. The current matcher selects by execution mode, not
host OS: composite discovery matches only when its mode specification contains
`windows`. Explicit single-file invocation bypasses this metadata; do not
invoke this Windows row directly on Linux.

The scenario passed within the original four-example Windows Phase-1 diagnostic
suite before this file/metadata split. No unchanged green assertion was rerun
solely for the split; this is not new native or cross-host execution evidence.
