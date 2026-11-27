# Suffixed literal match arms become unconditional wildcards

Status: source repair authored; execution under a rebuilt producer pending.

The actual budgeted-store native compilation failed in
`lib.scv.db_pages.db_page_decode` with
`B5b: match has multiple wildcard arms (arm 1)`. Its source matches a byte tag
against 1u8 through 5u8 and a final wildcard. The flat parser represents the
numeric arms as EXPR_SUFFIXED_LIT, but convert_flat_pattern had no case for
that tag and fell through to PatternKind.Wildcard. No source decoder match was
rewritten and the duplicate-default diagnostic remains strict.

The repair keeps suffixed literals as literal casts, then normalizes
integer-literal casts in HIR to typed IntLit predicates. Narrow casts retain
expression truncation/sign extension; 64-bit bit patterns are unchanged.
Noninteger operands, noninteger casts and unsupported widths remain explicit
casts for the existing diagnostic rather than becoming unconditional arms.

Five authored regression scenarios in
`test/01_unit/compiler/hir/suffixed_integer_pattern_spec.spl` cover bridge
preservation, the five database tags, signed/unsigned widths, 64-bit values,
and unsupported/noninteger/ordinary literal controls. They remain UNRUN.

Original executed failure and source-origin caveats:
`doc/03_plan/evidence/seven_plans/items247_store_compile_diagnostics_2026-10-20.md`.
A rebuilt producer and executed compiler/HIR/MIR acceptance are required before
this issue can close. The old producer cannot validate a compiler-source repair
by recompiling the unchanged decoder with its own old frontend.
