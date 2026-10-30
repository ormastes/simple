# One-element literal `[attr]` of a loop text var boxed as int (2026-10-25)

Status: OPEN. bug_db.sdn: DB reconciliation pending. Source workaround on
work/p3fix-g2slice (native_interface_slice.spl). Compiler root fix not written.

## Symptom
Phase 3 gen-2 self-build (run-28g2 attempt d, compiler gen-1b `S/r27/g2/simple.g1b`,
sha 45958454, source work/p3int28 e8ca110a681, SIMPLE_PARSE_SHARD_MAX=6): all 6
parse-shard children SEGV (exit -139, 2 rounds) on the full closure; hello's closure
does not reach the path. Backtrace (S/r27/g2/shim/bt.so, BT_TARGET=parse_shard_main):
strlen <- `rt_array_join_any+0x344` <- `native_slice_finish_decl_v1+0x154` <-
`native_interface_decls_v1` <- `native_source_interface_fact_ok_v1`. strlen arg
0x58a3ce958c288 = heap handle << 3.

`native_interface_decls_v1+0x4d0..0x528` (run-27e Stage-2 object): `rt_value_int_wide(attr)`,
`rt_array_new(1)`, `rt_array_push`, then `native_slice_finish_decl_v1(attr, arr)`:
the trailing `for attr in pending_attrs: ... [attr]` literal int-boxes its text element.
Only sources ending in top-level `@attr` lines (non-empty `pending_attrs` at EOF) hit it.

## Repro (Stage 2, S/r27/stage2-simple; untracked src/app/zz_g2slice in worktree simple-p3fix-g2slice)
- a/b/c: plain `for a in xs: f(a, [a])` with `xs: [text]` -> PASS (shape alone is not enough).
- d: the real shape (untyped `var logical = t` grown by `+` in a loop, pushed into
  `pending_attrs`, alias swap `cur_lines = pending_attrs; pending_attrs = []`, trailing
  `for attr in pending_attrs: [attr]`) -> SEGV.
- e: d with `val attr_text: text = attr; [attr_text]` -> PASS, identical output.

## Workaround
`src/compiler/80.driver/cache/native_interface_slice.spl`, tagged
`@workaround bug=one_element_literal_of_loop_text_boxed_as_int_2026-10-25`.

## Spec
`test/01_unit/compiler/driver/native_interface_slice_trailing_attr_spec.spl` (natural shape).
