# `std.fs` resolves ambiguously (file vs directory module) — two `File` classes collide

Date: 2026-09-01
Status: OPEN
Severity: Medium — `File.write_bytes` (and potentially other `File` statics)
silently resolves to the wrong class definition depending on which of two
co-existing `File` classes the interpreter picks.

## Evidence

```bash
bin/simple test test/01_unit/lib/common/archive/deflate_compress_spec.spl
```

```
CBOR ...
[31m✗ produces an archive the system unzip tool accepts and can extract[0m
    semantic: unknown static method write_bytes on class File
```

`test/01_unit/lib/common/archive/deflate_compress_spec.spl:20,124`:
```simple
use std.fs.{File}
...
File.write_bytes(out_path, archive)
```

Two DIFFERENT `class File` definitions both live under the `std.fs` namespace:

- `src/lib/nogc_async_mut/fs.spl:205` (flat file, module `std.fs`) — has a
  `static fn write_bytes(path: text, data: [u8]) -> bool` at line 249.
- `src/lib/nogc_async_mut/fs/path.spl:287` (module `std.fs.path`, re-exported
  from `src/lib/nogc_async_mut/fs/__init__.spl` which is ALSO reachable as
  `std.fs` since it's the package `__init__.spl` for the `fs/` directory) —
  has no `write_bytes` static.

Both `fs.spl` (a file) and `fs/` (a directory with its own `__init__.spl`)
exist side by side and both claim the `std.fs` module name. `use std.fs.{File}`
resolves to the WRONG one (the directory's re-exported `fs/path.spl::File`,
which lacks `write_bytes`), even though the flat `fs.spl::File` — the one with
`write_bytes` — is also in scope under the same name.

Same defect family as the `compiler_cross_module_private_symbol_collision`
warnings printed at interpreter startup for `Trace32Adapter`/`Trace32Parser`
(two classes with the same name across two modules; the interpreter resolves
members by NAME, not by originating module, so a method body from one
definition can execute against — or fail to be found on — an instance of the
other).

The mirrored sync module has the identical shape:
`src/lib/nogc_sync_mut/fs.spl` (flat, has `write_bytes`) vs.
`src/lib/nogc_sync_mut/fs/__init__.spl` + `fs/path.spl` (directory, no
`write_bytes`).

## Impact

Any caller that does `use std.fs.{File}` and expects the flat `fs.spl::File`
API (`write_bytes`, `read_bytes`, etc.) can silently get the `fs/path.spl`
`File` instead, failing at the first static method call not present on that
narrower class. Only discovered here because the deflate spec calls
`File.write_bytes` — other `std.fs.{File}` call sites that only use methods
present on BOTH classes would not surface the collision.

## Root cause (not fixed here)

This is a module-resolution architecture issue — a flat `<name>.spl` file and
a `<name>/` directory (with its own `__init__.spl`) both mapping to the same
dotted module path — not a small local bug. Fixing it needs a decision about
which one `std.fs` should mean (or renaming one of them, e.g. the directory
package to `std.fs.driver` or similar) and is out of scope for a test-triage
pass per `.claude/rules/testing.md` guidance on filing rather than risk-fixing
compiler/module-resolution defects.

## Not fixed here

`test/01_unit/lib/common/archive/deflate_compress_spec.spl` is left RED and
reported as a genuine failure. Not modified.
