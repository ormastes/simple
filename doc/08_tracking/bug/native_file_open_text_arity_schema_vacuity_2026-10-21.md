# File-open text ABI mismatch produces empty schema generation

Date: 2026-10-21
Status: pure-Simple source repair authored; native verification pending.

## Actual v3 failure

The isolated v3 `compiler_schema` binary generated 4,385 bytes of child-frame
templates instead of the checked-in 56,367-byte file. It exited zero, reporting
four base visitor kinds but zero HIR and AST carrier variants. The failed parity
receipt remains `build/nogc-hardening/hir-generator-parity-3.json` in
`/home/yoon/dev/simple-pure-redeploy-v3-20261021`; its temporary output must not
replace checked-in generated code.

GDB stopped that actual binary in `rt_io_file_open`. The caller chain was
`FileTextSession.open` through `std.nogc_sync_mut.sffi.fs.io_file_open`. The path
pointer identified the requested v3 HIR declaration source, but `x1` was zero
and the provider returned -1. Root/environment selection was correct.

The linked C provider declares `(path_ptr, path_len, mode)`. The Simple extern
declared `(path: text, mode)`. The older r17 producer omitted this provider from
its text-expansion registry, so read mode zero occupied the path-length register.
Opening an empty path failed. `read_file_text` converted the error to empty
text, and schema generation accepted an empty declaration universe.

## Pure-Simple repair

The canonical filesystem facade now declares the actual three scalar ABI words.
It obtains a byte pointer and UTF-8 byte extent using the existing runtime
`rt_string_data` and `rt_string_len` accessors. Their `Any` arguments preserve
the retained runtime text owner through the synchronous open call. The existing
semantic-arity guard recognizes that three operands are already expanded, so
newer producers do not expand them again. No C or Rust source changes are used.

The remaining `FileHandle.open` direct two-argument route now delegates to this
same facade. The focused native fixture exercises an existing non-ASCII UTF-8
path, exact content, descriptor close and missing-file rejection.

Visitor generation refuses a missing/zero-variant base carrier before creating
outputs. Fold generation preflights each dialect's carrier variants before
publishing fold files. The CLI reports failure for these refusals instead of
claiming vacuous success.

## Limits

No build or test was run by this repair's author. The v3 generator binary
predates the source fix and cannot establish its correctness. Full generated
file equivalence remains unverified until an updated admitted pure-Simple
producer and the repaired generator complete the guarded comparison.
