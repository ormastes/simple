<!-- codex-design -->
# DevHub launch mode detail

Parse the optional leading control argument, falling back to `DEVHUB_MODE`
and then `ordinary`. Reject unknown/missing values with exit 2. Exit 78 for
loading before candidate discovery. Ordinary retains candidate order and
admission; report selected identity once, forward remaining arguments with
shell argument boundaries intact, and preserve child status. Both verbose
and captured-diagnostics dispatch follow this same selection.

The focused shell harness creates a private repo fixture and actual process
markers, with local test-only provenance receipts. It checks default and
explicit dispatch, CLI precedence, spaces, verbose dispatch, unsupported
loading without probes, invalid values, exit propagation, and stale hashes.
These fixtures test wrapper behavior, not native Windows binary admission or
successful loading. Existing Windows transport coverage remains separate.
