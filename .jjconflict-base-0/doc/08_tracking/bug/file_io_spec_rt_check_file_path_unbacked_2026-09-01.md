# `file_io_spec.spl`: extern `rt_check_file_path` has no runtime backing

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/file/file_io_spec.spl`, 0/4 passing).

## Symptom

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/file/file_io_spec.spl
```

```
File I/O FFI Functions
  file existence checking
    ✗ should check if file exists
      semantic: unknown extern function: rt_check_file_path
    ✗ should return false for non-existent files
      semantic: unknown extern function: rt_check_file_path
  file size retrieval
    ✗ should get size of existing file
      semantic: unknown extern function: rt_check_file_path
    ✗ should return error for non-existent file
      semantic: unknown extern function: rt_check_file_path

4 examples, 4 failures
```

`src/compiler_rust/lib/std/src/file/__init__.spl:28` declares
`extern fn rt_check_file_path(path: text) -> bool` and calls it at line 115
(`file_exists`), but no runtime — Rust or C — defines `rt_check_file_path`
anywhere in the tree:

```bash
grep -rn "rt_check_file_path" src/runtime/ src/compiler_rust/runtime/
# no output
```

This matches the class of pre-existing "unbacked extern" defects tracked by
`scripts/check/check-unbacked-extern-ratchet.shs` / the broader
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`
population — a declared `extern fn` with zero runtime implementation, whose
call silently misbehaves (here it fails loudly with a compile-time "unknown
extern function" rather than the silent-nil case that bug tracks, but the
root defect class — declaring an extern nothing backs — is the same).

## Why not fixed here

Adding a real runtime implementation for `rt_check_file_path` (or rewiring
`file_exists` to call an existing backed primitive, e.g. `rt_file_exists`
used elsewhere in the same `std.file` package) touches the Rust/C runtime
layer, which is out of scope for a stdlib-spec triage pass focused on safe,
low-risk fixes. Note also that `src/compiler_rust/lib/std/src/file/__init__.spl`
is a different copy of the file module than `src/lib/**` (this repo carries
more than one `std.file` implementation reachable depending on module
resolution), so the fix location needs confirming against which copy is
actually loaded before editing.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/file/file_io_spec.spl
```
