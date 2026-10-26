# Lane FSDICT — `use std.fs` "resolves to a plain dict"

**Date:** 2026-07-27 · **Status:** DONE (library fixed, specs unblocked, compiler defect filed)

## Verdict on the reported symptom

`use std.fs` does **not** fail to resolve. It resolves to
`src/lib/nogc_sync_mut/fs.spl` and binds `fs` to that module's **namespace dict**
— which is the intended representation. `fs.file_exists(...)` and
`fs.read_file(...)` have always worked.

The red was two separate things:

1. **Missing members (library).** `exists`, `read_to_text`, `read_text`,
   `write_text` and `stat` were never defined in `std.fs`. Calling them produced
   `method 'exists' not found on type 'dict'` — which *reads* like a module
   resolution failure but is a missing-member error. `std.fs` had only
   `read_to_string / write_string / list_dir / read_file / write_file` plus the
   `Path/File/Dir/Walk/Glob` classes.
2. **Compiler defect (filed, not patched).** Even after adding the members, a
   module-namespace member call inside an sspec `it` block fails unless the same
   bare name is also in the flat global registry. See
   `doc/08_tracking/bug/module_namespace_member_call_in_spec_it_block_2026-07-27.md`.

No hijack of `std.fs` by another module, no dict-valued global shadow, no
missing `__init__`.

## Changes

- `src/lib/nogc_sync_mut/fs.spl` — added + exported `exists`, `read_to_text`,
  `read_text`, `write_text`. `stat` deliberately NOT added: `src/os/port/**`
  expects a `Result`-shaped `stat` (`.is_ok()`, `.unwrap().mtime`) that has no
  backing type in the tree, while `disk_boot_spec` expected a bare struct — two
  contradictory contracts, so the callers were moved to `fs.file_size` instead.
- Spec files: `fs.exists(` → `fs.file_exists(`; `fs.stat(img).size` →
  `fs.file_size(img)` wrapped in a real `expect`; literal `"cross-{triple}"` /
  `"compiler-rt-{triple}"` escaped to `{{triple}}` (they were being interpolated).
- Probes under `build/fsdict_probe/` (p1..pc).

## Before / after (`bin/simple run <spec>`, per-describe summary line)

| Spec | before | after |
|------|--------|-------|
| `test/integration/os/port/llvm/per_target_build_spec.spl` | 21 examples, 21 failures | 21 examples, **1** failure |
| `test/integration/os/port/llvm/cross_build_plan_spec.spl` | 14 examples, 14 failures | 14 examples, **0** failures |
| `test/integration/os/port/rust/smoke_rustc_spec.spl` | 4 examples, 3 failures | 4 examples, **2** failures |
| `test/integration/os/port/llvm/smoke_clang_spec.spl` | 5 examples, 0 failures | 5 examples, 0 failures (assertions now real) |
| `test/system/os/port/disk_boot_spec.spl` | 5 examples, 0 failures | 5 examples, 0 failures (assertions now real) |

35 previously-dead examples now actually assert.

## Genuine failures newly revealed

- **`per_target_build_spec` — "gates compiler-rt behind -simpleos triples"**:
  expected `src/os/port/llvm/build.spl` to contain `ends_with("-simpleos")`;
  actual: the file contains **no** `ends_with` at all — the compiler-rt build is
  not gated behind SimpleOS triples. Product gap in `src/os/port/**` (not owned
  by this lane).
- **`smoke_rustc_spec` — 2 examples fail with `semantic: variable 'code' not
  found`** from `val (out, err, code) = process.run(...)`. Tuple destructuring of
  `process.run` is not binding; the error also leaks into the *following* `it`.
  Separate defect, unrelated to `std.fs`.

## Blast radius

`use std.fs` appears in **321** owned `.spl` files: **96** under `src/**`,
**225** under `test/**`. Of the `src/**` sites, **11** files in `src/os/port/**`
call members that did not exist before this change (`fs.exists`, `fs.read_text`,
`fs.write_text`, `fs.stat`) — `exists`/`read_text`/`write_text` are fixed by the
library change; `fs.stat` in `bootstrap_verify.spl`,
`bootstrap_native_verify.spl` and `build_tools/simple_make.spl` is still
unresolvable and needs an owner decision on its contract.
