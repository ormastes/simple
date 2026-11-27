# simple-core archive built with GNU ar on Windows has no index for its (weak) runtime symbols (2026-11-22)

Status: FIXED in `scripts/check/check-simple-core-runtime-smoke.shs` (this change).

## Symptom

New Phase 1 seed (release `6816f70c47e`), Windows MSVC. The `cs` essential app was built against
the simple-core archive (`--runtime-bundle simple-core`, `SIMPLE_SIMPLE_CORE_PATH=<archive>`,
archive sha256 `abc4d9b868316326dcbbe7084ec1120f9cb5e2da65c539d8ddd21aaf75944239`). It compiled,
then failed to link:

```
Build failed: link failed: 1105 undefined symbol(s) with SIMPLE_NO_STUB_FALLBACK=1: ...
lld-link: error: undefined symbol: rt_alloc
lld-link: error: undefined symbol: rt_string_new_literal
```

## Root cause

The archive parts define their runtime functions as weak externals.
`llvm-nm -g --defined-only` lists `378 W` and `0 T` for `rt_*` names, for example
`00000000 W rt_alloc`. The script built the archive with `ar rcs`, and on this host the first `ar`
is msys2 GNU binutils. GNU ar leaves COFF weak externals out of the archive symbol index:
- `llvm-nm --print-armap` on that archive: 0 `rt_` index entries, `rt_alloc` absent.
- Re-archiving the same objects with `llvm-ar rcs`: 378 `rt_` index entries, `rt_alloc` present.

lld-link selects archive members through the index only, so it never pulled a member.

The repo's toolchain policy is clang/LLVM only, with GNU binutils never a silent substitute
(`missing_llvm_tool_error`, `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`).

GNU nm also misled the earlier required-symbol gate. It prints a COFF weak-external
definition as an address-less `w` line, the same shape as an undefined weak reference.

## Fix

- Build the archive with `llvm-ar` when it is on PATH, falling back to `ar`.
- In the CORE_REQUIRED gate, read definitions with `llvm-nm -g --defined-only` when available.
  Also require each symbol to appear in the archive index (`llvm-nm --print-armap`); a missing
  one fails with `error=core_required_symbol_not_in_archive_index:<name>`.

## Specs

- Reproducing: the gate replica on the GNU-ar archive above reports `missing_index=84`
  (`print_raw`, `rt_alloc`, `rt_array_data_ptr_text`, ...), so it FAILS.
- Generalization: on the same objects archived with llvm-ar it reports `missing_defined=0
  missing_index=0`, so it PASSES. The gate covers all 86 required symbols, not only `rt_alloc`.

## Open

Whether simple-core parts should define runtime symbols weakly on COFF at all is a codegen
question for the compiler owner. It is not changed here.
