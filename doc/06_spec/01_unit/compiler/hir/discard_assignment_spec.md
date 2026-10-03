# Discard assignment lowering

Requirement: REQ-HIR-DISCARD-001. Executable source:
test/01_unit/compiler/hir/discard_assignment_spec.spl.

The structured and flat parser forms must produce a unit block with exactly
one RHS statement. Compound discard must report a diagnostic. An ordinary
undeclared assignment target and a standalone underscore read must continue
to fail name resolution. An invalid discarded RHS must emit exactly one
diagnostic, proving the lowering did not visit it twice.

The native companion fixture checks the observable side effect count and
final-statement behavior. Expected stdout is `discard effects=1`.

Execution status: UNRUN. This is a reviewed scenario description, not a
generated execution report or a verification PASS.
