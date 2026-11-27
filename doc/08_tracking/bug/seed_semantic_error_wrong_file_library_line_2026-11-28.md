# Seed: semantic error in a library function reports the spec's path with the library's line

Status: verification-pending

## Symptom
A runtime semantic error raised inside a library function printed the entry
(spec) file with the library statement's line, e.g.
`semantic: test/01_unit/compiler/common/di_spec.spl:25:9: cannot iterate over this type`
for an error at `src/lib/nogc_sync_mut/compression/gzip/decompress.spl:25`.

## Root cause
`CompileError::semantic_with_context` (`src/compiler_rust/compiler/src/error.rs`)
filled a missing span from `CURRENT_NODE_SPAN` (the executing statement) but a
missing file from `CURRENT_FILE`, which is always the entry file.

## Fix
Fill the file from the executing function's owning module
(`current_coverage_file()`, which already falls back to the entry file and to
`<entry>` for in-memory source; `<entry>` now means "no file"). The path is shown
cwd-relative with `/` separators (owner keys are `\?\C:\...` on Windows).

## Tests
- Rust unit: `error::tests::semantic_with_context_uses_executing_module_file`
  (expects `decompress.spl:25:9`, not the spec path; fails on the old code).
- Manual e2e probe (spec calling a library fn that iterates an Option) printed
  `test/01_unit/compiler/scratch_attr/attr_lib.spl:6:5` on the new seed.
