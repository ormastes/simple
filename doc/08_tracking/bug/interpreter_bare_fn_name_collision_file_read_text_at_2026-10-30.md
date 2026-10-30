# Interpreter binds an imported function to a same-named function from another loaded module

## Status
Library collision removed 2026-10-30. The interpreter defect itself is open.

## Symptom
`test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl` failed all 7
examples with `semantic: nil is forbidden by the non-optional return contract of
'service'`.

## Root cause
`src/lib/nogc_async_mut/sosix/file_driver.spl` imports the Result-returning
`file_read_text_at` (`std.nogc_sync_mut.io.file_ops`, `-> Result<text, text>`).
`src/lib/nogc_sync_mut/sffi/fs.spl` defined a raw wrapper with the same bare
name (`-> text`). `std.spec` imports `std.nogc_sync_mut.sffi.fs`, so every spec
loads that module. Once it is loaded, the interpreter binds the driver's call to
the raw wrapper, even though the driver imports the other one. Importing straight from
`std.nogc_sync_mut.io.file_ops` did not help either. `match ... case Ok(bytes)`
matches no arm on a plain `text`, so `SosixHostedFileDriver.service` returned
nil. The same code passes under `simple run` without `std.spec`.

This reproduces the mechanism that
`bare_name_registry_collision_trigger_conditions_2026-07-30.md` could not pin
down, for functions: the trigger is a second module with a same-named
top-level `fn` being loaded anywhere in the process.

## Fix (library)
The raw SFFI wrapper is renamed `file_read_text_at_raw` (same pattern as
`file_size_raw`) in `nogc_sync_mut/sffi/fs.spl`, and in the re-export lists in
`gc_sync_mut`, `gc_async_mut` and `nogc_async_mut` `sffi/fs.spl`. Nothing called
it by its old name.

## Specs
- Reproduction: `test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl` (0/7 before, 7/7 after).
- Generalization: `test/01_unit/lib/nogc_async_mut/sosix/file_read_text_at_collision_spec.spl`
  (FAILs with the old name restored, PASSes with the rename).

## Open (interpreter)
An explicit `use a.b.{f}` must bind `f` to `a.b`'s definition no matter which
other modules define `f`. Until the interpreter enforces this, any two stdlib
modules that share a top-level function name can break each other's callers.
Unblock condition: the interpreter's function lookup resolves through the
importing module's import table before the global bare-name table.

## Side note
The spec example "round-trips through a native Windows-style backslash path"
leaves files named like `\tmp\sosix_file_driver_winpath.txt` in the working
directory on macOS.
