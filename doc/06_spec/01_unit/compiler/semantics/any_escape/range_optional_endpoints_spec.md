# Any escape analysis of optional range endpoints

Executable: `test/01_unit/compiler/semantics/any_escape/range_optional_endpoints_spec.spl`.
Requirement: REQ-MC-ANY-001.

The spec constructs typed HIR and invokes the real Any expression checker.
It checks an absent start, absent end, both absent endpoints, and an Any-typed
expression at each present endpoint. Absent bounds yield no diagnostics;
present Any endpoints must produce E-MC-ANY-001.

Phase 1 evidence on 2026-10-06: five failures before the repair, five passes
after it. Native bootstrap validation remains pending. No placeholder passes
or source-text assertions are used.
