# Module-level `val` dict export is unresolved through `use module.{name}` / `use module.*`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED (2026-11-11, lane ne15) — dict-valued module `val` exports now
resolve through named and wildcard `use`; 8/9 examples pass on the fresh seed.
The 1 residual failure is a separate `dir.create`/`dir.exist` Windows issue, not
this import gap. See addendum.
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/shell/file_system_spec.spl`, 0/9 passing).

## Symptom

`src/lib/nogc_sync_mut/shell/mod.spl` builds a "namespace" as a module-level
`val` holding a dict literal:

```
val file = {
    "exist": exist,
    "write_text": write_text,
    ...
}
```

and `src/lib/nogc_sync_mut/shell/__init__.spl` re-exports it (`export env,
file, dir`). `file.spl`'s own header comment documents this as the intended
usage: `use std.shell.{file}` then `file.exist(path)`.

Importing it this way — via named import (`use std.shell.{file}`) or
wildcard (`use std.shell.*`) — fails to resolve at all:

```
error: semantic: variable `file` not found
```

confirmed both via `bin/simple test` on
`test/01_unit/lib/std/shell/file_system_spec.spl` (all 9 examples fail
identically) and via a minimal 3-line repro run directly:

```
use std.shell.{file}
fn main():
    print(file.exist("nope"))
```
```
[CODEGEN BODY] Function 'main' body compilation failed: GlobalLoad: unresolved
  identifier 'file' (not a global, function, const-data name, or import)
...
error: semantic: variable `file` not found
```

Same result with `use std.shell.*` in place of the named import — rules out
a named-import-list-specific bug; the dict `val` itself is not being
threaded through module export/import at all.

## Scope note

Only one file in the tree (`file_system_spec.spl`) actually exercises this
import pattern, so the blast radius currently measured is small — but the
mechanism (a module `val` bound to a dict/struct literal used as a
pseudo-namespace) is a documented, encouraged pattern in `shell/file.spl`'s
own header comment, so any other module following the same
"build a namespace as a `val` dict, re-export it" idiom would hit the same
wall.

## Not fixed here

This is a compiler/interpreter import-resolution gap (dict-valued `val`
export not visible to a consuming module), not a stdlib logic bug — fixing
it needs work in the Rust seed's module-import / codegen path, which is out
of scope for a stdlib-focused triage pass. Left failing; do not paper over
by inlining `use std.shell.file.*` (imports the raw functions, not the
`file.exist(...)` namespace call style the spec and the module's own doc
comment describe) without also fixing or removing the doc'd namespace
pattern.

## Repro

```
bin/simple test test/01_unit/lib/std/shell/file_system_spec.spl
# Results: 9 total, 0 passed, 9 failed — all "variable `file` not found"
```



## Addendum 2026-11-11 (lane ne15) — FIXED; dict-val export resolves via `use`; 1 residual example is a different defect

**Verification actually run** (worktree simple-p3-ne15-20261111, tip
f7640d20a458, fresh seed 46fe8f6b6def, seed-smoke):

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe test \
  test/01_unit/lib/std/shell/file_system_spec.spl --mode=interpreter --no-cache
# Results: 9 total, 8 passed, 1 failed
```

(was: `9 total, 0 passed, 9 failed` — every example `variable 'file' not
found`). All `file.*` namespace calls through the documented
`use std.shell.{file}` pattern now resolve and behave correctly (exists,
write/read text, append, copy, rename, recursive dir create, dir list all
green). The compiler/import-resolution mechanism this doc filed is fixed.

**Residual 1/9** — "should create and remove directory" fails at
`assert_true(dir.exist(test_dir))` after `dir.create(test_dir)`, both with
and without a pre-created `build/test_tmp` parent. That is a
`dir.create` (= `dir_create(path, false)`, non-recursive) / `dir.exist`
(= `dir_exists`) Windows fs-layer behavior issue in
`src/lib/nogc_sync_mut/shell/dir.spl` — unrelated to the val-dict export
gap. An isolated `use std.shell.{dir}` probe also surfaced a separate
`dir_exist` resolution error inside the shell module graph on the seed.
Lead for a new row (stdlib fs / seed), not fixed in this pass; out of scope
for this doc.
