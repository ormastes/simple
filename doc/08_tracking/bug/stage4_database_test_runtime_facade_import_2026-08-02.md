# Stage 4 database test runtime-facade import gap

Status: fixed — next Stage 4 closure pending  
Severity: P1 bootstrap blocker  
Fix owner: `/root/stage4-database-test-runtime-facade` — CLAIMED

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

The file explicitly imports that name from `std.io`. The root cause was an
incomplete public contract in `std.nogc_async_mut.io`: the root facade exported
host helper names that the async package did not itself re-export from the sync
owner. The repair aligns that package facade with the complete host-helper
surface promised by `std.io` instead of adding concrete-owner bypasses to each
consumer.

The same focused build then exposed `Array.enumerate` as unavailable in the
`core-c-bootstrap` lane. Both database variants now use an equivalent indexed
loop, removing that unnecessary link dependency.

Post-fix evidence:

- pure-Simple Stage 3 host-facade probe: 36 compiled, linked, output `true`;
- pure-Simple Stage 3 exact async database probe: 48 cached, 2 rebuilt, linked;
- async host-facade regression: 1 passed;
- database start/end regression: 2 passed.

The linked pure-Simple probe still exposes a separate native Option-return
representation mismatch in `end_run`; it is tracked independently in
`native_inlined_option_return_representation_mismatch_2026-08-02.md` and does
not re-open this facade/import compile blocker.

The full Stage 4 build was not repeated after the repository's three-cycle cap;
the next scoped Stage 4 session must provide the authoritative closure result.

Retained final log:
`build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-runtime-facade-final.log`.
