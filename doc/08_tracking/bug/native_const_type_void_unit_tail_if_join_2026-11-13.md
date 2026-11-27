# native_const_type_void_unit_tail_if_join_2026-11-13 (P1, fix-implemented-verification-pending -- MIR lowering hardened; native Phase 2 / Stage 3 rebuild verification pending)

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
2. Compiler hardening (landed 2026-11-27):
   - `src/compiler/50.mir/mir_lowering_stmts.spl`: added `mir_join_slot_is_unit`,
     hardened `mir_join_slot_is_payloadless` / `mir_merge_arm_types`, and gated
     `lower_if` and `lower_if_chain` (`if_has_else`, `chain_has_else`,
     `result_slot_unit`, `result_slot_payloadless`, `emitted_default_def`,
     `emit_copy`, `set_local_type`) from the slot's non-optional `MirType` value
     so `Unit` / `Never` / else-less join slots never receive `Const` or `Copy`
     definitions while preserving side effects and legitimate non-`Unit` value
     joins.
   - `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`: applied the
     same `result_slot_unit` / `result_slot_payloadless` /
     `merge_result_is_payloadless` / `set_local_type` guards across
     `emit_switch_dispatch`, `emit_if_chain_dispatch`, `lower_match`, and
     `lower_enum_match_flat`.
   Takes effect natively after a Phase 2 / Stage 3 rebuild from tip.

## Verification
- Fixture probe build on the frozen Phase 2: failing variants as tabled.
- Lint rebuild on the frozen Phase 2 with the workaround: see PR.
- Prevention spec `test/01_unit/compiler/50.mir/native_const_type_void_unit_tail_if_join_spec.spl`
  counts `Const`/`Copy` defs into `Unit` locals across all documented tail shapes
  (`v_a_help` else-less call preserving call, `v_f_two`, `p1_exact`, mixed
  `Unit`/`i64` `if`/`else` and `if`/`elif`/`else`, unit-tail `match`, plus
  positive non-`Unit` `if`/`else` value control): `12 examples, 0 failures`
  (`--mode=interpreter`, 2026-11-27).
- Native Phase 2 / Stage 3 rebuild verification remains pending (`fix-implemented-verification-pending`).

## Related
- `native_const_type_void_checked_join_host_facade_2026-11-07.md` (same error
  class, native-only, else-less if in loop / early-return enum tail).
