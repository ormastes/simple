# native_const_type_void_unit_tail_if_join_2026-11-13 (P1, open -- source workaround landed; compiler hardening in a follow-up PR; Phase 2 rebuild pending)

## Symptom
The frozen Windows Phase 2 pure-Simple compiler
(`/c/dev/wt-lane2/build/diag-phase4/phase2.exe`) native-building
`src/app/cli/lint_entry.spl` (LLVM, `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`) failed
codegen with `E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void;
use an explicit MIR Cast for numeric conversion` in
`app.cli.lint_entry.print_command_help` and
`compiler.frontend.core._ParserDecls.enum_module_body.parser_lower_unit_decl`
(log `/c/dev/wt-lane2/build/diag-phase4/jl_lint/build.log`). Both sources are
correctly typed; the interpreted MIR lowering + LLVM pass produce 0 const defs
into void locals (PR #8819 investigation), so the defect is in the
natively-compiled lowering.

## Native reproduction (frozen Phase 2, fixture `test/fixtures/native_const_void_join/`)
No MIR/LLVM dump knob exists in the frozen binary (`SIMPLE_KEEP_LLVM_IR` /
`SIMPLE_LLVM_KEEP_STAGE` only keep IR that was emitted; codegen fails first),
so the shape was bisected with one function per variant. Each failing variant
names itself in the backend error.

| variant | shape | native Phase 2 |
|---|---|---|
| `v_a_help` | unit fn, TAIL `if/elif/elif/else` of print arms (print_command_help copy) | FAIL |
| `v_f_two` | unit fn, TAIL `if/else` of print arms | FAIL |
| `v_e_help_tail` | `v_a` + explicit `()` tail after the chain | ok |
| `v_c_help_early` | `v_a` as else-less ifs with early `return` | ok |
| `v_b_decl` / `v_d_decl_assign` | mid-body if/else of discarded i64 calls | ok |
| `p1_exact` | exact parser_lower_unit_decl copy with same-signature local stubs | FAIL |
| `p2_no_if` | `p1` without the if/else | ok |
| `p5_typed_tail` | `p1` with `val r: i64 = if ...` and explicit `()` tail | ok |

The tail join of a unit fn is lowered with `expected_type = Some(Unit)`
(`lower_block_expected(fn_.body, fn_.return_type)`), giving a Unit merge slot.
In `lower_if` / `lower_if_chain` every `Const 0` default def into that slot is
gated by `expected_type == None` (dominating def) or by
`merge_result_is_payloadless(result)` (a `local_mir_type_of(..) ?? i64`
re-lookup). Hosted, both gates keep the Unit slot def-free; natively one of
them is miscompiled and a `Const 0 : i64` lands in the void slot. Which of the
two predicates is miscompiled is NOT yet confirmed (no native MIR dump); the
backend diagnostic now names `dest` and the Const's own type to settle it on
the next occurrence.

## Fix
1. Source workaround (this PR, behaviour-preserving, tagged
   `# @workaround bug=native_const_type_void_unit_tail_if_join_2026-11-13`):
   explicit `()` unit tail in `print_command_help`; `val registered_unit: i64 =
   if ...` plus explicit `()` tail in `parser_lower_unit_decl`.
2. Compiler hardening (follow-up PR `work/mir-unit-join-no-const`): the
   lower_if / lower_if_chain default defs are decided from the slot's own
   non-optional MirType value (`mir_join_slot_is_payloadless`), never from the
   Option compare or the `??` re-lookup. Hosted behaviour is identical; the
   native lane no longer depends on the miscompile-prone predicates. Takes
   effect after a Phase 1/2 rebuild from the tip.

## Verification
- Fixture probe build on the frozen Phase 2: failing variants as tabled.
- Lint rebuild on the frozen Phase 2 with the workaround: see PR.
- Prevention spec `test/01_unit/compiler/50.mir/native_const_type_void_unit_tail_if_join_spec.spl`
  (follow-up PR) counts Const/Copy defs into Unit locals for the tail shapes.

## Related
- `native_const_type_void_checked_join_host_facade_2026-11-07.md` (same error
  class, native-only, else-less if in loop / early-return enum tail).
