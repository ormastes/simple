# TUI Core Runtime Smoke Failure

Date: 2026-05-27
Status: Resolved for the audited startup-size TUI paths.

## Summary

The startup/size audit builds small Simple TUI binaries. Both audited TUI lanes
now pass:

- `build/startup_size_perf_audit/simple_tui_standalone` exits successfully.
- `build/startup_size_perf_audit/simple_tui_app` exits successfully when fed
  `quit` on stdin.

## Evidence

Run:

```sh
sh scripts/check-startup-size-performance-audit.shs
```

Report:

- `doc/09_report/startup_size_performance_audit_2026-05-27.md`

Current measured sizes from the latest audit:

- Simple standalone TUI core-c-bootstrap: `14336` bytes.
- Simple full TUI app core-c-bootstrap: `14360` bytes.

## Impact

The generated standalone TUI size/startup lane and the simplified full TUI app
can now be counted as executable evidence. The audited full TUI app hot path has
a two-module entry closure and no parser/render-stack dependency. The fuller
parser-backed startup path is still not part of the hot startup path because it
is a separate rich-TUI concern rather than the dependency-size baseline.

## Next Checks

- Keep parser-backed SDN loading out of the startup-hot TUI path unless it has
  separate simple-core coverage.
- Add a focused parser simple-core bug if the parser-backed path becomes a
  required startup feature again.
