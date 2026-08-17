# Choosing a file-read API and what its bytes mean

Practical guide for `src/lib/nogc_sync_mut/io/file_ops.spl` readers, written
after the 2026-08-16 signature unification. If you are about to call something
named `file_read*`, read the table first — several same-named functions exist
across the tree and they have not always agreed.

## The canonical entry points

| Call | Returns | Use it for |
|---|---|---|
| `file_read_text(path)` | `text` | UTF-8 / ASCII content you will treat as a string |
| `file_read_bytes(path)` | `[u8]` | Binary content. **This is the canonical byte read.** |
| `file_read_bytes_i64(path)` | `[i64]` | Callers that operate on `[i64]` byte streams (SCV, `cache_validator`) |

`file_read_bytes` and `file_read_bytes_i64` read the same underlying bytes. They
differ only in element type. Both are exported from
`std.nogc_sync_mut.io.file_ops`.

## Which one should new code use

Use `file_read_bytes`. The `[u8]` shape is the canonical one and matches the
same-named definitions in `std.nogc_sync_mut.sffi.io`, `.../ffi/io.spl`, and
`io_runtime.spl`, so a module that imports any of them behaves identically.

Reach for `file_read_bytes_i64` only when you are extending code that already
threads `[i64]` byte streams. Inside `src/lib/scv/` that is the established
pattern: read `[i64]`, then narrow with the module-local `scv_i64_bytes_to_u8`
where a `[u8]` is needed. Do not introduce the `[i64]` shape into new code.

## History, and why the shapes exist at all

Before 2026-08-16 the `file_ops` definition of `file_read_bytes` returned
`[i64]` while three other same-named definitions returned `[u8]`. Co-compiling a
closure containing two of them produced an ambiguous-dispatch warning and, worse,
a silently differently-shaped value. The fix kept the `[u8]` name canonical and
renamed the raw shape to `file_read_bytes_i64`, migrating ten `src/lib/scv/`
modules and `src/compiler/80.driver/cache/cache_validator.spl`.

Two consequences worth knowing:

- The font and rendering path (`io/font_sffi.spl`, `sffi/spl_fonts.spl`,
  `text_layout/font_renderer.spl`) imports from `std.nogc_sync_mut.sffi.io`,
  which was already `[u8]`. It was not affected by the change.
- `src/app/release/github.spl` passes the result straight to
  `std.common.base_encoding.bytes_to_text`, which takes `[u8]`. The unification
  silently *corrected* a pre-existing mismatch there.

## Sign extension is the failure mode to watch

The `[i64]` shape is where byte bugs hide. A byte above `0x7F` that is sign
extended arrives as a negative `i64`, and every downstream length, hash, or
comparison is then wrong for exactly half the byte range — while ASCII fixtures
keep passing. When you narrow an `[i64]` stream, mask explicitly:

```
out.push((raw[i] & 0xFF).to_u8())
```

That masking pattern is what `file_read_bytes` itself does internally, and what
`scv_i64_bytes_to_u8` does for SCV.

## The optional text read has its own name

`file_read` returns `text`, never `text?`. If you want an absence case, call
**`file_read_opt(path) -> text?`**.

Until 2026-08-16 three compiler modules defined a module-local
`fn file_read(path: text) -> text?`, so `file_read` existed in two incompatible
return types at once. Because the function registry is keyed on NAME ALONE,
which one a call site received depended on the import closure of the compiling
module — and a caller written against `-> text` has no nil branch, so being
handed the optional definition drops the absence path silently. Those three were
renamed to `file_read_opt`; do not reintroduce an optional-returning
`file_read`. Guarded by
`test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl`.

## Reaching the readers through the `app.io.mod` shim

`src/app/io/mod.spl` is a backward-compatibility shim that re-exports the
`file_ops` readers for `use app.io.mod (...)` callers. As of 2026-08-16 it
re-exports **both** byte shapes — `file_read_bytes` and `file_read_bytes_i64`.
Before that it carried only the `[u8]` one, so shim callers could not reach the
shape SCV consumes.

A symbol needs both an import line and an export line in that file to be
reachable; one without the other is a dangling re-export. The guard spec asserts
both lines exist for each byte reader.

## Related

- Byte-contract system spec:
  `test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl`
  (mirror: `doc/06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md`,
  plan: `doc/03_plan/sys_test/scv_render_file_read_coverage.md`)
- Definition-count guard:
  `test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl`
- Open defect on the text family (23 definitions, two return types):
  `doc/08_tracking/bug/file_read_has_23_definitions_with_two_return_types_2026-08-16.md`
