# native-build worker timeout fires far earlier than the configured budget

- **ID:** native_build_worker_timeout_misaccounted_2026-08-09
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found by:** gui/web/2D vulkan showcase sweep, 2026-08-09
- **Area:** `src/app/cli/native_build*` worker supervision
- **Severity:** medium — large-closure native builds are killed mid-compile
  and the error message reports a budget that was never reached, sending the
  reader to raise `--timeout` uselessly

## Evidence

- `native-build --timeout 21600 ... main_gui.spl`: worker killed with
  `error: native-build worker timed out after 21600s before producing a
  binary` after ~40 minutes (~2400s) of wall time — ~9x early.
- `native-build` (default 7200s budget) on the web standards showcase entry:
  killed with `timed out after 7200s` after ~60 minutes (~3600s) — ~2x early.
- The surviving web worker (same entry, `--timeout 21600`) was still
  compiling at 2h09m / 99% CPU, so the compiles genuinely need >1h; the
  early kills are not the worker being idle.

## Suspects

The supervisor wraps the worker in `timeout --kill-after=10s <budget>s` and
the CLI measures elapsed time itself for the error message; the two clocks
disagree by different factors per run (2x and 9x observed), so the bug is
more likely in the CLI's elapsed computation (e.g. a stale start timestamp
shared across attempts via the build lock in `build/.simple-bootstrap-locks`,
or CPU-time vs wall-time confusion) than in `timeout(1)`.

## Repro

```
src/compiler_rust/target/bootstrap/simple native-build --timeout 21600 \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/ui_showcase/hosts/main_gui.spl \
  --strip --output build/showcase/showcase_gui
```

Watch wall time until the "timed out after 21600s" error appears (observed at
~40 min).

## Related

- `native_build_fixed_cost_floor_hides_incrementality_2026-08-08`
- `native_build_cache_scope_key_renders_corrupt_persistent_cache_2026-08-08`
