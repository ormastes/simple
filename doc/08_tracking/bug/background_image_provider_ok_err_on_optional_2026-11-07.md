# background_image_provider matches Ok/Err on an Optional subject

- **ID:** background_image_provider_ok_err_on_optional_2026-11-07
- **Severity:** P2 (2 Stage 2 MIR errors in run 13)
- **Status:** open

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
