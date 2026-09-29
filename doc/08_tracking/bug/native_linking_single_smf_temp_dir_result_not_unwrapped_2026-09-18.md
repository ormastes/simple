# `link_to_native` single-SMF branch compares an un-unwrapped `Result` to `""`

**Date:** 2026-09-18
**Found by:** linker lane A3 while trying a real link through the new adapter.
**Status:** fixed 2026-09-19 (lane B3).

## Symptom

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`, single-SMF
branch:

```simple
val tmp_dir = create_temp_dir()   # returns Result<text, text>
if tmp_dir == "":                 # compares the Result itself; never unwrapped
```

At runtime this crashes with `method contains not found on type enum`. It happens
when `link_to_native` is called directly with `NativeLinkConfig.default()` and a
single `.smf` input.

## Fix direction

`match create_temp_dir(): case Ok(d): ... case Err(e): return Err(e)`, plus a spec
that links one SMF through `link_to_native`.

## Fix

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`: all three
`val tmp_dir = create_temp_dir(); if tmp_dir == "": ...` call sites in
`link_smf_bundle` (the multi-SMF/.lsm branch and both single-SMF branches) now
unwrap the `Result<text, text>` explicitly:

```simple
val tmp_dir_result = create_temp_dir()
if tmp_dir_result.is_err():
    return Err("Failed to create temp dir for SMF objects: {tmp_dir_result.unwrap_err()}")
val tmp_dir = tmp_dir_result.unwrap()
```

Covered by
`test/01_unit/compiler/backend/linker/native_linking_internal_spec.spl`
("links a single SMF wrapping a real ELF object without crashing on the
Result comparison"), which builds a real single-`.smf` file (via `SmfWriter`,
embedding a real ELF object in its Code section so `ObjectProvider.get_object`
takes the code path that reaches `create_temp_dir`) and links it through
`link_to_native`, confirming no `method contains not found on type enum`
crash and a runnable output. Same fixture/spec mirrored to
`test/unit/compiler/backend/linker/native_linking_internal_spec.spl`.
