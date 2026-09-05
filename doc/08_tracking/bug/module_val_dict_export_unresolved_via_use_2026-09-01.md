# Module-level `val` dict export is unresolved through `use module.{name}` / `use module.*`

**Status:** OPEN (SIMPLE-CAPABILITY / compiler import resolution)
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
