# mono call inference: pinned stage2 cannot infer generic call type args (2026-10-31)

Status: FIXED IN SOURCE (2026-11-01); still present in the pinned/frozen stage2, so every
`@workaround bug=mono-call-inference-20261031` tag stays until the stage2 refresh (phase 3
owner reverts). Revert-ready: yes.

## Root bug
Tag reason (all 13 sites): "pinned stage2 cannot infer generic call args from match-arm/field
bindings; annotate explicit type arguments". Introduced by 571c205b7f7 ("explicit generic type
args at 29 pinned-stage2 call sites"), extracted from an E-MONO-033 phase-1 full-CLI build log:
the pinned stage2 monomorphizer reported E-MONO-032 ("argument inference has no concrete local")
for generic free-function calls whose type argument is only implied by an argument, e.g.
`_dbfs_finish_result(Err(FsError.Busy))`, `array_sort_by(less, comparator)` inside a generic
body, `rt_channel_try_recv(id)` / `channel_try_recv_by_id(id)`.

## Workaround sites (explicit `f<T>(..)` type arguments)
- `src/app/office/sheets/calc_access_session_host.spl:216`
- `src/app/office/sheets/calc_access_session_host.spl:230`
- `src/app/office/sheets/calc_session_host.spl:99`
- `src/app/office/sheets/calc_session_host.spl:108`
- `src/lib/nogc_async_mut/array.spl:184`
- `src/lib/nogc_sync_mut/concurrent/channel.spl:216`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:293`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:327`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:357`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:541`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:556`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:611`
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:763`

## Current-source status
The 40.mono pass was deleted (200a05f5bc8 "delete monomorphization", ab9305d783e, 56c0499ebd1);
generics are erased, and no `E-MONO-0xx` diagnostic exists in `src/compiler` any more.

Evidence: seed `bin/simple.exe` v1.0.0-rc.1 running the CURRENT pure-Simple `src/compiler`
in-process (parse -> HIR -> MIR lowering, provider `lib.fut` + consumer), release/1.0.0,
2026-11-01: the un-annotated shapes `finish(Err(RErr.Busy))` / `finish(Ok(true))` with
`fn finish<T>(r: Result<T, RErr>) -> Result<T, RErr>`, and `sort_by(xs, <lambda a, b>)` with a
recursive generic `sort_by<T>`, produce zero consumer diagnostics. Final spec assertion form is
UNRUN (coordinator memory HOLD on test runs); fixtures ran green in the probe.
Not covered by the fixture: the return-type-only shape `channel_try_recv_by_id(id)` at
`calc_session_host.spl` / `calc_access_session_host.spl` (T appears only in the result; the
binder is later read as `i64`) -- keep its explicit `<i64>` unless re-probed.

Regression spec: `test/01_unit/compiler/50.mir/generic_call_arg_inference_spec.spl`.
