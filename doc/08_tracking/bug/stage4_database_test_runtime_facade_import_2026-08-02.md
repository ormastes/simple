# Stage 4 database test runtime-facade import gap

Status: open — self-host parity blocker  
Severity: P1 bootstrap blocker  
Fix owner: `/root/stage4-database-test-runtime-facade` — HANDOFF AFTER ITERATION CAP

## Reproduction

The no-stub x86 Stage 4 cycle 2 build parsed all 1,430 source files, crossed
the prior `BackendResult` payload blocker, and then stopped during HIR:

```text
src/lib/nogc_async_mut/database/test.spl: unresolved name: rt_timestamp_now
```

Retained log:
`build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-backend-payload-identity.log`.

## Repair boundary

The database modules must import and call the public `std.io` facade names
`time_now_unix_micros` and `getpid`, rather than relying on undeclared runtime
primitive names. Apply the same repair to the async and sync source variants,
then compile-check both variants before the final retained-cache Stage 4 retry.

## Focused verification

- `test/01_unit/lib/database/test_database_duration_spec.spl`: 2 passed,
  including a real `start_run`/`end_run` path through the portable facades.
- `simple_seed check src/lib/nogc_async_mut/database/test.spl`: pass.
- `simple_seed check src/lib/nogc_sync_mut/database/test.spl`: pass.

Stage 4 remains the authoritative closure gate, so the claim stays active until
the final no-stub build crosses this module and produces its candidate.

## Final Stage 4 result for this session

The third and final bounded build cycle rejected the replacement facade name:

```text
src/lib/nogc_async_mut/database/test.spl:
unresolved name: time_now_unix_micros
```

The file explicitly imports that name from `std.io`, and both Rust-seed
compile checks pass, so the remaining defect is self-host parity in resolving a
name re-exported by the `std.io` facade. A fresh scoped session should determine
whether the bounded repair is a direct import from each concrete IO owner or a
HIR re-export-resolution correction, add a self-host regression, refresh Stage
3 if compiler code changes, and then begin a new capped Stage 4 cycle set.

Retained final log:
`build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-runtime-facade-final.log`.
