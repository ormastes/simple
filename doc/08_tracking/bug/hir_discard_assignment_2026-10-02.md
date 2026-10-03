# Discard assignments fail full native HIR lowering

Status: implemented; native and SSpec validation pending.

Windows LLVM Phase3 module attempt.EWRTku/5, using Phase2 producer e7ec89c1,
reported unresolved name `_` in aspect_pack_io.spl at137,202,207. Each site
is a discard assignment of rt_io_file_close(fd), not a match wildcard.

Structured assignment, the bootstrap scalar dispatcher, and the flat parser
expression-assignment path all lowered the left side as a variable read.
The shared lower_hir_assignment_kind now recognizes only a plain `_` target.
It lowers the RHS once into a unit-valued block containing one expression
statement. The block is necessary: generic block lowering promotes a final
HirStmtKind.Expr into a value tail, which must not expose the discarded RHS.
Compound discard reports an error. Ordinary target resolution and tuple
destructuring remain unchanged; `_` remains invalid as an ordinary read.

REQ-HIR-DISCARD-001: structured and flat assignments evaluate RHS once and
discard its value; invalid compound/undeclared targets still fail.

Unit evidence: test/01_unit/compiler/hir/discard_assignment_spec.spl inspects
real lowered HIR, exact statement count, unit-block shape, and diagnostics.
Native acceptance: test/fixtures/compiler/discard_assignment_effect_once.spl
must compile and print `discard effects=1`; this also exercises a final
discard statement. Both suites are currently UNRUN; source inspection is
not native acceptance. No live bootstrap source was modified.

Scope excludes bare enum pattern and AtomicI64 method-resolution failures;
those are separately owned compiler investigations. Review owner: root.
