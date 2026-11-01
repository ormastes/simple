# Stage2 types a Poll.Ready payload binder as unsubstituted T, so a nested bare Ok/Err match is ambiguous

- **ID:** stage2_poll_payload_typeparam_match_2026-11-01
- **Priority:** P1 (blocks phase-3 stage3 self-build)
- **Status:** open; source workaround landed in `src/lib/nogc_async_mut/io/buffer.spl`
- **Owner area:** `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (enum-match lowering:
  type of a generic enum payload binder used as a nested match subject), with the HIR/RTI pass that
  assigns payload binder types for `Poll<T>` patterns
- **Found by:** phase-3 run 14c, frozen stage2 `C:/dev/p3new/stage2.exe` (ef0681fc0e1), release/1.0.0 at 5fad50cca24

## Symptom

```
[go-to-end] failed stage=mir module=lib.nogc_async_mut.io.buffer: MIR lowering error: enum match:
bare variant 'Ok' is ambiguous (declared in multiple enums); qualify it as EnumName.Ok;
subject expression at .../src/lib/nogc_async_mut/io/buffer.spl:239:23 has type T
```

Same error (and the `Err` twin) at buffer.spl lines 190, 222, 239, 372, 391, 408, 433, 450.

## Minimal repro

```simple
use std.async.poll.{Poll}
use std.common.crypto.aes_gcm.{AesGcmResult}   # any second enum declaring Ok/Err

fn show(p: Poll<Result<[u8], text>>) -> text:
    match p:
        case Poll.Ready(result):
            match result:            # result typed `T`, not Result<[u8], text>
                case Ok(b): "ok"
                case Err(e): "err"
        case Poll.Pending: "pending"
```

Without a colliding `Ok`/`Err` enum in the closure the bare variant resolves to its sole owner and
the bug is masked; that is why a small closure compiles and the full stage3 closure does not.

Repro command (8 GB cap, ~4-6 min): probe entry importing `AsyncBufferedReader/Writer` plus
`AesGcmResult`, run with `stage2.exe native-build --entry-closure --entry <probe> --source src/lib
--source src/compiler --source src/app --keep-going --go-to-end` under `measure.ps1 -CapGB 8`.
Before the workaround: 16 `go-to-end failed stage=mir` lines in buffer (8 sites x Ok/Err).
After: 0. (`compile --format=smf` does not reach MIR for this module, so it shows 0 either way.)

## Expected

The payload binder of `Poll.Ready(x)` on a subject of type `Poll<Result<A, E>>` has type
`Result<A, E>` (the enum's `T` substituted with the subject's type argument), and the nested match
resolves `Ok`/`Err` against `Result`.

## Workaround

`# @workaround bug=stage2_poll_payload_typeparam_match_2026-11-01` in buffer.spl: the arm becomes
`case Poll.Ready(_):` and the payload is pulled out by a concrete helper
(`_poll_bytes_payload` / `_poll_unit_payload` / `_poll_count_payload`) into a local with a declared
`Result<..>` type, then matched. Behaviour is identical (the helpers are only reached on the Ready
arm). A typed binder alone (`val r: Result<..> = result`) is not relied on, since the binder type is
what is wrong. A repo-wide grep of src/lib, src/compiler, src/app and src/plugins found no other
`case Poll.Ready(x):` + nested `match x:` site.

Regression spec: `test/01_unit/lib/nogc_async_mut/io/async_buffer_poll_payload_wa_spec.spl`
(not executed in the landing session).

## Revert

Once the payload binder type is substituted, revert the helpers and restore the direct
`case Poll.Ready(result): match result:` form.
