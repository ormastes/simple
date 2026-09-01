# Path/File type migration inventory

## Existing support

The standard library already provides the canonical object types in
`src/lib/nogc_async_mut/fs/path.spl`, re-exported by `std.fs.path`:

- `Path(path: text)` stores a normalized filesystem value and provides typed
  path operations (`file_name`, `extension`, `is_file`, and so on).
- `File(path: Path)` is the typed file-operation façade. Its `read`, `write`,
  `copy_to`, `exists`, and `delete` methods cross the raw `text` runtime
  boundary only at the implementation edge.

The raw runtime ABI (`rt_file_*`, `rt_dir_*`) intentionally remains text-based;
it is an FFI boundary and is not a public domain API. There was no `_path`
literal syntax. Numeric suffixes already have a parser transport, but string
tokens do not carry suffixes.

## Bounded migration in this change

- The parser accepts `"..."_path` and lowers it to the imported canonical
  `Path(path: "...")` constructor. This is syntax sugar, so normal name
  resolution and type checking still apply.
- `src/app/desugar/mod.spl:desugar_file` now takes `Path` for both input and
  output. It converts to text only at `rt_file_read_text`/`file_write`, the raw
  ABI boundary.
- `examples/06_io/smux/main.spl` now discovers and loads configuration through
  `Path`/`File`, including `_path` literals.

## Remaining text-path scope

The migration is intentionally incremental. The raw ABI declarations and
legacy compatibility façades remain text-based. A repository-wide tracked
scan at implementation time found 3,351 `rt_*` path/file/dir extern
declarations and 11,995 function declaration lines with a path/file/dir
parameter typed as `text`; those are outside this bounded change and require
lane-by-lane API ownership decisions. The focused changed surface has no
remaining public `Path`/`File` parameter typed as `text`.

## Tests

`test/01_unit/compiler/parser/path_literal_spec.spl` covers construction,
typed path methods, and composing a literal with `File.new`.
