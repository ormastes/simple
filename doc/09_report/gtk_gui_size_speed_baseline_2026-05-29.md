# GTK GUI Size And Speed Baseline

Date: 2026-05-29

## Summary

| Runtime | Status | Binary bytes | Iterations | Total us | Notes |
|---|---|---:|---:|---:|---|
| Simple web renderer | failed | n/a | 4 | n/a | simple_run_failed |
| GTK | unavailable | 14472 | 200 | n/a | no_display |

## Simple Output

- [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Cannot infer type: TypedInteger(4294967295, U32)
- [memory-guard] SIMPLE_LIB=/home/ormastes/dev/pub/simple/src contains 600+ .spl files — consider narrowing scope to avoid memory bloat

## GTK Output

- gtk_render_status=unavailable
- gtk_reason=no_display

## Notes

- Set SKIP_SIMPLE_NATIVE=0 to add Simple native binary bytes; default skips the slow native build.
- GTK size is the minimal linked executable size, not the full shared-library closure unless inspected with ldd.
- GTK speed is unavailable on headless hosts without a display.
- Simple speed measures the pure software HTML-to-pixel path and records the shared render optimization profile.
