# env/platform.spl no longer routes through io.* semantic owners

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl

## Observed
src/lib/nogc_sync_mut/env/platform.spl imports `std.env.types` directly and
no longer uses `std.nogc_sync_mut.io.env_ops.{home_raw, cwd_raw}`,
`io.process_ops.{process_run_raw}`, `io.sysinfo_ops.{hostname}`. The
ownership-routing contract the spec pins has lapsed; whether the new
direct-import layout is the intended design needs an owner decision.

## Unblock condition
Confirm intended ownership layout; either restore owner routing or update
the spec pins deliberately.
