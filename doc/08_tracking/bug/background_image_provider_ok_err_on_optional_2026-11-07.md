# background_image_provider matches Ok/Err on an Optional subject

- **ID:** background_image_provider_ok_err_on_optional_2026-11-07
- **Severity:** P2 (2 Stage 2 MIR errors in run 13)
- **Status:** fixed

## Symptom

`src/os/compositor/background_image_provider.spl:271` does
`match File.read_bytes(source): Ok(bytes): ... Err(read_error): ...`, but
`std.fs` `File.read_bytes` is declared `-> [u8]?`
(`src/lib/nogc_sync_mut/fs/flat.spl:226`). Stage 2 fails with
`enum match: bare variant 'Ok' is ambiguous ... has type Optional` (and `Err`).

## Analysis

The compiler is right: `Ok`/`Err` are not variants of an Optional. The source
comment says it matches Result arms because the runtime value on a missing file
was observed as a Result `Err`, i.e. it works around a runtime Option/Result
marshalling gap. Either the call must move to a Result-typed API
(`std.io.file` `File.read_bytes -> Result<[u8], IoError>`) or the arms must be
`Some`/`nil` after the runtime contract of `rt_file_read_bytes` is confirmed.
Not changed in the MIR ambiguity fix because it changes runtime behaviour of the
compositor and needs a runtime check.

## Fix (2026-11-07)

Both runtimes return the bare byte array or nil for `rt_file_read_bytes`
(`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs:2112`, interpreter
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1417`), matching the
declared `[u8]?`. So the `Ok/Err` match matched neither arm: in the interpreter
`resolve` raised "missing return in non-unit function" and
`wm_background_image_provider_spec` passed only 2/8. The source now binds
`if val bytes = File.read_bytes(source)` and falls through to the existing
unreadable path (last-good / loud failure); the spec passes 8/8.
