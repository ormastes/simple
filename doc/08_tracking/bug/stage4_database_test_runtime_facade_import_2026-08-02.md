# Stage 4 database test runtime-facade import gap

Status: reopened — full-graph facade collision reproduced (2026-08-03)
Severity: P1 bootstrap blocker  
Fix owner: `/root/option_native_codegen_rootcause` — CLAIMED

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

## Reopened full-graph diagnosis (2026-08-03)

The 50-module probe does not contain the same module-key collision as the full
graph.  With both `io.spl` and `io/__init__.spl` loaded, the file facade's
`use ...io.*` hop resolves back to the file facade instead of the directory
facade.  Its plain host-helper exports therefore form a self-cycle and HIR
never reaches the concrete `time_ops.spl` / `sysinfo_ops.spl` declarations.
The reserved canonical bug identifier is
`stage4_database_test_runtime_facade_import`; this owner has reopened the same
incident rather than creating a second competing bug.  The deployed seed's
canonical `bug_add` app was not allowed to retain its write: its SDN serializer
truncated unrelated existing long rows while checkpointing.  Both attempted
DB/WAL mutations were restored, so a working pure-Simple bug app must add this
row later without damaging existing records.

Retained final log:
`build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-runtime-facade-final.log`.

### Exact 1,431-source graph correction

The retained cycle-2 graph does **not** load either
`lib.nogc_async_mut.io.__init__` or `std.nogc_sync_mut.io.__init__`. Its
relevant discovery order is the database consumer, the async `io.spl` root,
the concrete sync time/sysinfo owners, the sync `io.spl` root, then the async
sysinfo/time compatibility children. Consequently the earlier regression was
not representative: it supplied both missing `__init__` surfaces and direct
package owners, so the re-export chase never exercised a plain root export
whose transitive child origin becomes known later.

The shared defect is discovery-order sensitivity in
`ModuleSurfaceBuilder.resolve_export_origins`: its package/name index contains
only direct declarations and its single pass visits the early async root before
the late compatibility child has recorded the concrete sync owner. The repair
must converge export origins across the loaded surface graph with a strict
module-count bound and fail closed on ambiguity; it must not add another
consumer- or runtime-tier-specific HIR fallback.

The exact focused graph converges in two fixpoint passes after the initial
direct/import-origin pass: the first promotes the late async time/sysinfo child
origins and resolves the early root, and the second observes no changes. The
same two-pass result holds with the relevant discovery order reversed. Package
`__init__` facades are deliberately excluded from the promoted-child index;
otherwise a later pass would incorrectly report the stable facade and its real
child as two owners of the same package export.
