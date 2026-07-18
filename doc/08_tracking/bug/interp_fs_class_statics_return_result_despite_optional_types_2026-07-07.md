# Interpreter: `fs` class-static methods typed `Optional`/`bool` actually return runtime `Result::Ok`/`Err`

**Date:** 2026-07-07
**Severity:** medium — silently defeats truthiness checks on file-existence/IO
guard code; found while wiring the image-background-provider PPM loader
(`src/os/compositor/background_image_provider.spl`) onto `fs.File`.
**Status:** OPEN — workaround applied at the call site, root cause not fixed.

## Symptom

`std.nogc_sync_mut.fs.File` declares statics with `Optional`/`bool` return
types, e.g.:

- `fn read_bytes(path: text) -> [u8]?`
- `fn write_bytes(path: text, data: [u8]) -> bool`
- `fn delete(path: text) -> bool`

At runtime the interpreter actually returns a `Result::Ok(..)` /
`Result::Err(..)` value from these calls, not a plain `Optional`/`bool`. Two
observable failures follow from this type/value mismatch:

1. **`if val` on an `Err` result is TRUTHY.** Repro: call
   `File.read_bytes("/definitely/missing/path")`. `match val: Ok(_) => ...,
   Err(_) => ...` correctly reports `Err`, but a plain `if val:` guard on the
   very same value reports truthy (non-nil `Result::Err(...)` is not falsy the
   way a real `nil` Optional would be). Any call site written against the
   declared `-> [u8]?` signature and guarding with `if val` — the idiomatic
   pattern for an Optional — silently takes the "success" branch on a missing
   file.
2. **`File.delete(path)` crashes instead of returning `bool`.** Declared
   `-> bool`, but internally the Result-unwrap path attempts to read a `.path`
   property off a plain `text` value and crashes with:
   ```
   error: unknown property or method 'path' on String
   ```

## Why it matters

The declared signatures (`Optional`, `bool`) are exactly the shapes callers
are told to guard with `if val` / `if File.delete(...)`. Both idioms are
broken by the actual runtime representation, and the failure mode is silent
for `read_bytes` (wrong branch taken, no crash) and loud-but-wrong for
`delete` (crash blaming `String`, not the real Result-unwrap bug).

## Workaround applied

`background_image_provider.spl`'s loader does not use `if val` on
`File.read_bytes`; it `match`es explicitly on `Ok(bytes) => ...` /
`Err(_) => ...` and treats any `Err` as "no provider data, fall through to
loud-marker". It also avoids `File.delete` entirely (uses the free
`file_delete` extern instead of the class-static).

## Next step

Find the `fs.File` static dispatch/marshalling path (likely in the same
family as the Rust-seed interpreter's Result/Optional value representation —
cf. `interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md`
for a related interpreter-representation bug found in the same lane) and
either (a) make the declared `Optional`/`bool` return types real at the call
boundary (unwrap `Result` into the declared shape before returning to
`.spl` code), or (b) fix the declared signatures to `-> Result<[u8], text>`
etc. so callers `match` instead of `if`. Also fix the `.path`-on-`String`
crash in the `delete` unwrap path regardless of which option is chosen.
