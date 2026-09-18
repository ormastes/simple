# `link_to_native` single-SMF branch compares an un-unwrapped `Result` to `""`

**Date:** 2026-09-18
**Found by:** linker lane A3 while trying a real link through the new adapter.
**Status:** open. Reproduced with no lane-A3 code involved.

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
