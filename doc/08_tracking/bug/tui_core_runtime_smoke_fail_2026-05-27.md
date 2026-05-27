# TUI Core Runtime Smoke Failure

Date: 2026-05-27

## Summary

The startup/size audit builds small Simple TUI binaries, but the runtime smoke
does not pass:

- `build/startup_size_perf_audit/simple_tui_standalone` exits with status `3`.
- `build/startup_size_perf_audit/simple_tui_app` exits with status `139`.
- Both failures produced no stderr in the audit run.

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

The size direction is correct, but the TUI lane cannot be counted as production
ready until the small binaries also execute successfully. This blocks using the
TUI measurements as final proof for startup-speed and dependency-elimination
requirements.

## Next Checks

- Isolate whether exit `3` in the standalone lane comes from core-C bootstrap
  runtime startup, ANSI string output, or unresolved runtime hooks.
- Debug the `simple-core` full TUI app segfault before adding stricter TUI size
  gates.
- Once fixed, rerun the startup/size audit and the existing TUI closure guard.
