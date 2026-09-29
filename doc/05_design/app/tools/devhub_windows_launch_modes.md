<!-- codex-design -->
# DevHub launch mode detail

Parse the optional leading control argument, falling back to `DEVHUB_MODE`
and then `ordinary`. Reject unknown/missing values with exit 2. Exit 78 for
loading before candidate discovery. Ordinary retains candidate order and
admission; report selected identity once, launch the native runtime directly,
forward remaining arguments, and preserve child status. An explicit
`DEVHUB_SH` remains a compatibility escape to the POSIX wrapper. Both native
and POSIX dispatch keep the same mode selection contract.

The focused shell harness creates a private repo fixture and actual process
markers, with local test-only provenance receipts. It checks default and
explicit dispatch, CLI precedence, spaces, verbose dispatch, unsupported
loading without probes, invalid values, exit propagation, and stale hashes.
The Windows fixture also exercises native dispatch without `sh.exe`, argument
and exit propagation, and missing-artifact fail-closed behavior. These tests
do not claim native PE startup or successful loading.
