# `libsimple_runtime.so` hides all 350 C-defined `rt_*` providers

- Filed: 2026-09-06
- Measured on: aarch64-unknown-linux-gnu, `--profile bootstrap`,
  `CARGO_PROFILE_BOOTSTRAP_LTO=off`, `--features runtime-symbol-table`
- Severity: blocks the owner directive "Simple must use dynamic libs, not static
  archives" — the shared library cannot replace the static archive as-is.

## Symptom

Measured same-tree (this branch, one target dir — do not mix with the older
bootstrap-baseline figures of 1646/2211):

`libsimple_runtime.so` exports 1676 `rt_*` symbols. The static
`libsimple_native_all.a` that Stage 4 actually links exports **2244** — a gap of
**568**. Exactly **350** of that gap is the set of `rt_*` symbols defined by the
C translation units compiled into the shared library itself, of which **0 are
exported**. (The other ~218 are `native_all`-only names — driver hooks,
`rt_cocoa_*`, `rt_win32_*` — that were never in the runtime crate; they are a
separate matter from this bug.)

```
$ nm -D --defined-only libsimple_runtime.so | awk '$2=="T"&&$3~/^rt_/' | wc -l
1676
$ nm --defined-only libruntime_sffi_c.a   | awk '$2=="T"&&$3~/^rt_/' | wc -l
350
$ comm -12 <exported> <c-defined> | wc -l
0
```

The code is present but local, not global:

```
$ nm libsimple_runtime.so | grep rt_time_now_nanos
00000000001c48e0 t rt_time_now_nanos      <-- lowercase t: local, not exported
```

Linking against the `.so` therefore fails for any C-provided name:

```
mold: error: undefined symbol: rt_time_now_seconds
```

## Root cause

`src/compiler_rust/runtime/build.rs` compiles ~40 owned C translation units and
links them with `cargo:rustc-link-lib=static:+whole-archive=runtime_sffi_c`, so
the objects genuinely are in the library.

Two mechanisms could demote them to local `t`; this was settled by measurement,
not inference:

- **Compile-time visibility — ruled out.** `build.rs` passes no
  `-fvisibility=hidden`; the only `.flag()` call in the whole file is
  `-xobjective-c` (line 441).
- **rustc's cdylib version script — confirmed.** `cargo rustc … --crate-type
  cdylib -- --print link-args` shows rustc passing
  `--version-script=<target>/deps/rustcXXXXXX/list` (alongside the new
  `-soname,libsimple_runtime.so.0`). rustc builds that list from its own
  `#[no_mangle]` set, and a version script's `local: *` clause binds every
  unlisted symbol locally — which is precisely the lowercase `t` that `nm`
  reports.

This is a **single cross-platform root cause**: rustc does the same thing with a
generated `.def` on Windows and `-exported_symbols_list` on macOS.

## What does NOT fix it

- `-Wl,--export-dynamic-symbol=rt_*` — tried, measured, **no effect** (export
  count unchanged at 1676). On a shared library that flag controls *binding*, not
  export; it only adds to `.dynsym` for executables. `--dynamic-list` has the
  same semantics.
- Shipping a hand-written or generated `.def` on Windows — rustc already passes
  its own `.def`; a second one conflicts. It would also have to be derived from a
  *textual* source scan (`collect_defined_runtime_symbols`), which
  over-approximates by construction, and an over-approximating `.def` is a hard
  link error.
- An exported symbol-table accessor — there is none:
  `nm -D … | grep -iE 'symbol_table|symbol_lookup|symbol_entries'` returns
  nothing, so the 350 providers are unreachable from outside the library by any
  route, not merely unlinkable.

## Candidate fixes (not implemented — they touch files other lanes own)

1. **build.rs-generated `#[no_mangle]` Rust shims.** Compile the C definitions
   under a prefix (e.g. `-Drt_foo=c_rt_foo`) and generate a thin
   `#[no_mangle] pub extern "C"` forwarder per symbol, so rustc's own export
   machinery picks them up. Cross-platform, no linker flags, and the shim list is
   derived from the real archive rather than a text scan.
2. **Ship the C runtime as its own shared library** (`libsimple_runtime_c.so`)
   built from the same sources, with the cdylib linking it dynamically. Cleaner
   separation, but splits the ABI across two files and complicates consumers.

Option 1 is preferred; it keeps a single artifact and a single SONAME.

## Consequence for the selection lane

`src/compiler_rust/compiler/src/pipeline/native_project/**` must **not** select
`libsimple_runtime.so` for a direct native link until this closes — the link will
fail on the first C-provided `rt_*`. The static archive remains correct.

## Related

- Design: `doc/05_design/runtime/dynamic_library/shared_runtime_libraries.md`
- Check: `scripts/check/check-runtime-shared-library.shs` (asserts the export
  count is non-vacuous and above a floor; it would catch a total collapse of the
  export table, but by design does not assert C/Rust parity — that is this bug)
