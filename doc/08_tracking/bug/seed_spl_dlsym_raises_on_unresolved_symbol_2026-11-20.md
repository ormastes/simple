# Seed interpreter `spl_dlsym` raises on an unresolved symbol instead of returning 0

- **Found:** 2026-11-20, DHR P4 (`DynGenerationI64SlotV1`, PR #10514)
- **Host:** Windows 11, x86_64-pc-windows-gnu, `bin/simple.exe` (Rust seed interpreter)
- **Status:** open

## Symptom

`_sffi_dlsym_checked` (`src/lib/nogc_sync_mut/sffi/dynamic.spl:162`) is written to return
`Err("E-SFFI-001: unresolved foreign symbol: <name>")` when `spl_dlsym` returns `<= 0`.
Under the seed interpreter, resolving a name that a loaded library does not export instead
aborts the spec with a runtime error. The `Err` branch is never reached.

## Repro

In a spec run on the seed, load `kernel32.dll` with `DynLib.load_checked`, then resolve a name it
does not export (for example `NoSuchExport_dhr`) through the checked resolver, as
`DynlibGenerationHostV1.resolve_i64` does. Expected: `Err(...)`. Actual: a runtime error that ends
the spec.

## Impact

The checked-resolve error path of `DynI64FnSlot` / `DynGenerationI64SlotV1` cannot be tested on
the seed. The P4 spec currently triggers the refusal path with an unsupported arity instead, so
the lease-release-on-refused-resolve case is still covered. The unresolved-symbol branch is not.

## Next step

Make the seed's `spl_dlsym` extern return 0 for a missing export, matching the C runtime's
`dlsym`/`GetProcAddress` contract, instead of raising. Then add an unresolved-symbol case to
`test/01_unit/lib/nogc_sync_mut/kernel_plugin/dynlib_generation_spec.spl`.
