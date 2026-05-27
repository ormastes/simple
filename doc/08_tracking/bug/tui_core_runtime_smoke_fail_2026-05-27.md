# TUI Core Runtime Smoke Failure

Date: 2026-05-27

## Summary

The startup/size audit builds small Simple TUI binaries. The generated
standalone ANSI lane now passes, but the fuller `run_tui` simple-core app still
does not:

- `build/startup_size_perf_audit/simple_tui_standalone` exits successfully.
- `build/startup_size_perf_audit/simple_tui_app` exits with status `139`.
- The full TUI failure produced no stderr in the audit run.

## Evidence

Run:

```sh
sh scripts/check-startup-size-performance-audit.shs
```

Report:

- `doc/09_report/startup_size_performance_audit_2026-05-27.md`

Current measured sizes:

- Simple standalone TUI core-c-bootstrap: `26864` bytes.
- Simple full TUI app simple-core: `92312` bytes.

## Impact

The generated standalone TUI size/startup lane can now be counted as executable
evidence. The fuller `run_tui` app cannot be counted as production-ready until
the simple-core segfault is fixed.

## Next Checks

- Debug the `simple-core` full TUI app segfault before adding stricter TUI size
  gates.
- Once fixed, rerun the startup/size audit and the existing TUI closure guard.
