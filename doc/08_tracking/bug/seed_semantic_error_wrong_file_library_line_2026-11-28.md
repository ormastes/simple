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
Fill the file from the module that lexically wrote the statement
(`private_call_caller()`, the lexical-coverage rule: closure origin stamp, then
module top level, then the executing fn owner, then the entry file, else
`<entry>` = no file). The first version used `current_coverage_file()`, which
follows CURRENT_EXEC_MODULE; a closure inherits that from its invoker, so an
`it` body run by std.spec would have pointed at the spec framework (Opus review). The path is shown
cwd-relative with `/` separators (owner keys are `\\?\C:\...` on Windows; `\\?\UNC\srv\share` shows as `//srv/share`).

## Tests
- Rust unit: `error::tests::semantic_with_context_uses_lexical_module_file`
  (expects `decompress.spl:25:9`, not the spec path; fails on the old code).
- Manual e2e probe (spec calling a library fn that iterates an Option) printed
  `test/01_unit/compiler/scratch_attr/attr_lib.spl:6:5` on the new seed.
- Rust unit: `semantic_with_context_uses_lexical_module_inside_closure`
  (library frame + spec closure origin -> names the spec).
- e2e: an `it` body error printed `attr_spec.spl:15:9` (the spec), not std.spec.
- Not covered: "variable not found" errors carry no position at all (separate
  constructor); out of scope here.
