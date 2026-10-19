# Return operand projections

Authored manual for `test/01_unit/compiler/mir/return_operand_enum_extension_spec.spl`,
linked to REQ-002 in `doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.
Execution and generated documentation: UNRUN.

1. Construct Copy(local 7) and Move(local 11) independently. Require tags 1/2,
   their exact local IDs, and the nonconstant sentinels.
2. Project an absent return. Require kind 0, local -1, constant kind 0, text 0.
3. Project signed integers, Float and FloatLexeme, both booleans, nonempty and
   empty text, and Zero. Require their exact kind and scalar representation;
   preserve the original floating lexeme.
4. Project nonempty Array, Tuple, and Struct constants. Require distinct
   constant kinds 6/7/8 and the existing `zeroinitializer` projection string.
5. Project Goto, Unreachable, and Abort. Require the intentional non-return
   sentinels, including return kind -1.

These are projection tests, not backend aggregate-value serialization proof.
The independent injected-variant regression is described in
`enum_match_fallthrough_trap_spec.md`.
