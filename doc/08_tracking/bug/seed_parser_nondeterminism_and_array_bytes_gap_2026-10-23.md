# Rust seed: nondeterministic module parser, missing rt_array_bytes_* externs, and layout restrictions (multi-line constructs, empty-array position, reserved words)
## Open 2026-10-23 — needs owner triage

**Found:** 2026-10-22/23, lane `wt-sqlite-format-20261022`
(`work/sqlite-format-reader-20261022`), while building
`std.nogc_sync_mut.database.sqlite_format` (DB-A/DB-B gates).

## 1. Nondeterministic parse / "expected Comma, found RBracket"

The seed reports `parse: Unexpected token: expected Comma, found RBracket`
for module files whose bytes are *unchanged between a passing and a failing
run*. The same file (e.g. `schema.spl`, `writer.spl` under any name) passes
10/10 runs in one minute and fails 6/6 a few minutes later, with no edits in
between. Consequences observed while debugging:

- The error also fires for *undefined symbols/types* in signatures (e.g. a
  struct field removed, a `Result` closed with `]` instead of `>`), with no
  line number, making root-cause a coin flip against the nondeterminism.
- `use pkg.{symbol}` imports are lazy: a module that is imported but whose
  symbols are never referenced is never fully parsed, so "it imports fine"
  probes can be false positives. Forced imports (`use pkg.{used_symbol}`)
  are required for honest parse checks.
- Empirically, reducing a failing module's use of `Result<..., SqliteError>`-
  returning helper fns and restructuring `match` arms lowered the failure
  rate, but did not eliminate it; this is included as a data point, not a
  documented rule.

**Lane impact:** spec runs had to be retried; a spec is recorded green on a
run with `failed=0`. All seven sqlite_format specs reached green and stayed
green across consecutive runs in the same window. The suite must be re-run
when the seed is fixed to confirm stability.

## 2. Missing externs: rt_array_bytes_validate family (dynamic-SFFI array contract)

`std.io_runtime.file_write_bytes` (and the whole
`nogc_sync_mut.sffi.file_bytes` native write path) calls
`rt_array_bytes_validate` / `rt_array_bytes_basis_len` / `rt_array_bytes_basis_ptr`
/ `rt_array_bytes_copy_checked`, which the seed binary does not export:

```
semantic: unknown extern function: rt_array_bytes_basis_len
```

Text reads are also affected end-to-end: `file_read_text`-style round trips
return `""` for a file that was written correctly (verified on disk). Byte
reads (`file_read_bytes_result`) and text writes (`std.nogc_sync_mut.fs` ->
`file_write_text`) work, which is how the writer gate's python oracle exports
its image (hex dump via text write; python reconstructs the binary).

**Lane workaround (documented, not hidden):** the writer spec validates its
image in-memory through the bytes-based reader plus the external python
sqlite3 oracle; no shipped library code depends on the broken paths.

## 3. Layout restrictions (deterministic; easy to hit)

- Multi-line function signatures and multi-line call expressions are parse
  errors (single-line only).
- `[]` empty-array literals are legal only in typed `var x: [T] = []`
  positions, not as bare expressions or call arguments.
- Struct field access auto-unwraps `Option<struct>` after a nil check, but
  tuple `.0`/`.1` on `Option<scalar>` and numeric index on `Option<struct>`
  are hard errors.
- `export use pkg.{...}` silently drops names when written multi-line; the
  re-export must be single-line (or the dropped symbols surface later as
  "function not found").
- Reserved words that cannot be used as field/param/local names in some
  positions: `feature`, `def`, `next`, `rowid`.

## Proper fix (out of lane ownership)

Seed parser determinism + diagnostic quality, the rt_array_bytes_* dynamic
array ABI, and the text-read path are owned by the compiler_rust/runtime
seed maintainers. Several are already tracked as in-flight seed gaps; this
note ties them to a concrete consumer and records the observed behavior
matrix so the fixes can be verified.
