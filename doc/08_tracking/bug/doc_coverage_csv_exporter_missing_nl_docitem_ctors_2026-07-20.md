# doc_coverage csv_exporter: undefined `NL` import + DocItem missing create_class/create_enum

## Symptom

`test/01_unit/app/doc_coverage/csv_export_spec.spl` fails all 28 examples with:

```
semantic: variable `NL` not found
```

and 2 of those 28 additionally show (once the `NL` blocker is worked around mentally):

```
semantic: unknown static method create_class on class DocItem
semantic: unknown static method create_enum on class DocItem
```

Sibling spec `test/01_unit/app/doc_coverage/json_export_spec.spl` fails with the same
family of "Cannot resolve module" symptom at the import-path layer (see below), and is
likely to hit the same or a similar downstream issue once its import path is corrected.

## Root cause 1 (test-file layer, already fixed in this file)

`test/01_unit/app/doc_coverage/csv_export_spec.spl` imported via:

```
use doc_coverage.reporting.csv_exporter.{export_coverage_csv}
use doc_coverage.types.doc_item.{DocItem, DocKind}
```

which fails module resolution (`error: semantic: Cannot resolve module:
doc_coverage.reporting.csv_exporter`) from a `test/` caller, even though the module
exists at `src/app/doc_coverage/reporting/csv_exporter.spl` and is imported
successfully *without* the `app.` prefix from sibling files inside `src/app/**`
itself (e.g. `src/app/doc_coverage/reporting/csv_exporter.spl` imports
`doc_coverage.types.doc_item.{DocItem}` with no prefix and that resolves fine at
the source layer). From `test/`, the working convention (matching
`test/01_unit/app/doc_coverage/compiler_integration_spec.spl`) requires the
`app.` prefix. This part was fixed here (value-preserving import path edit only):

```
use app.doc_coverage.reporting.csv_exporter.{export_coverage_csv}
use app.doc_coverage.types.doc_item.{DocItem, DocKind}
```

`json_export_spec.spl` has the identical un-prefixed pattern
(`use doc_coverage.reporting.json_exporter...`) and fails identically; it was left
untouched (out of shard scope) but the same one-line prefix fix likely applies.

## Root cause 2 (genuine source bug, NOT fixed — out of test-shard scope)

After the import-path fix, `src/app/doc_coverage/reporting/csv_exporter.spl` itself
fails to compile:

```spl
# src/app/doc_coverage/reporting/csv_exporter.spl
use doc_coverage.types.doc_item.{DocItem}
use std.string.{NL}                                    # <-- NL not exported by std.string

fn export_coverage_csv(items: [DocItem]) -> text:
    var csv = "name,file,line,kind,is_public,has_sdoctest,has_inline_comment,tags{NL}"
    ...
        csv = "{csv}{row}{NL}"
```

`std.string` (`src/lib/string.spl`) does not define/export an `NL` constant — grep
over `src/lib/string.spl` and `src/lib/common/` finds no `NL` definition. Every
example in the spec constructs a CSV string via `export_coverage_csv`, so every
example trips this same "variable `NL` not found" semantic error.

## Root cause 3 (genuine test/source mismatch, NOT fixed)

`test/01_unit/app/doc_coverage/csv_export_spec.spl` lines 248 and 256 call:

```spl
val item = DocItem.create_class("MyClass", "/src/std/test.spl", 10, 5, "pub")
val item = DocItem.create_enum("Status", "/src/std/test.spl", 10, 5, "pub")
```

but `src/app/doc_coverage/types/doc_item.spl` only defines `create_function` (line
25) and `create_struct` (line 42) as static constructors — no `create_class` or
`create_enum`. These are real missing API surface, not a naming/rename issue (no
`create_class`/`create_enum`-shaped function exists anywhere else in that file to
rename to).

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/app/doc_coverage/csv_export_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — src/** out of test-shard scope)

1. Add a `NL` (or equivalent) newline constant export to `std.string`
   (`src/lib/string.spl`), or change `csv_exporter.spl` to use a literal `"\n"` /
   existing newline helper instead of importing a nonexistent `NL`.
2. Either add `DocItem.create_class` / `DocItem.create_enum` static constructors
   (mirroring `create_function`/`create_struct`), or remove/rewrite the two
   related `it` blocks in the spec once the correct API is confirmed with the
   doc_coverage module owner (do NOT silently delete — file/confirm first).

## Affected specs

- `test/01_unit/app/doc_coverage/csv_export_spec.spl` (in shard, import path fixed,
  still failing on root causes 2 and 3 above)
- `test/01_unit/app/doc_coverage/json_export_spec.spl` (same import-path symptom,
  not in shard, untouched)
