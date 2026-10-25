# Field read through `T?` after a nil check reads the Option box (int accumulators lost)

- Date: 2026-10-25
- Status: open (compiler); workaround at one site
- Found by: Phase 3 broad sweep (corpus run on Stage 3 bypass binary probe18)

## Symptom
In programs compiled BY the Stage 3 compiler (whose own code was built by Stage 2), every
`x = x + <variable>` loses its write. For example, `while k < 3: a = a + k` gives `a == 0`, and so
does the straight-line `c = c + y`. The produced binary also prints
`[simple-runtime][error] rejected invalid array handle before dereference ... (value_bits=0x1)`.
`x = x + <literal>` and `x = y + x` are unaffected. The same programs built by Stage 2 are correct.
Corpus programs hit: loops, strarr, dictit, arr2d, acc, acc2, acc4 (S/r27/sweep).

## Root cause
`10.frontend/desugar/collection_desugar.spl` (Pattern B) rewrites `x = x + <ident>` into a bare
`x.merge(<ident>)`. `lower_unresolved_array_merge` then picks integer addition only when
`mir_type_is_scalar_numeric(local_mir_type_of(x))` is true for both operands.
In the Stage 3 binary that predicate always returns 0. gdb on `simple.probe18` shows that its
`type_: MirType?` argument is an Option.Some enum box (`kind=4, enum_id=0xd, disc=1, payload`).
The source does `if found == nil: return false` and then `found.kind`, and that read takes the
BOX's word rather than the payload's. As a result the merge falls through to `rt_array_extend_i64`
on an int receiver, and the sum is dropped.

This is the same family as the `hir_cache_load_parsed_v1` crash (X3), which does `loaded == nil` and then
reads `.path`. Both access a field of a `T?` value after a nil test, without binding the payload.

## Workaround
`mir_type_is_scalar_numeric` binds the payload with `if val present_type = type_`
(`@workaround bug=optional_field_read_after_nil_check_reads_option_box_2026-10-25`).
Spec: `test/01_unit/compiler/50.mir/merge_desugar_int_accumulator_spec.spl`. It fails only when built
natively by an affected compiler.

## Open
- Compiler fix: either field access on a `T?` local (after a narrowing nil check) must unwrap the payload,
  or the type checker must reject it.
- A census of `if x == nil: return ...` followed by `x.field` on `T?` values is still to be done.

## Bug DB
DB reconciliation pending: no `bug_db.sdn` row was added for this ID in this change.
