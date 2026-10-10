# BUG-IT-6 — 50.mir: a multi-parameter generic struct's field is lowered as a struct named after the TYPE PARAMETER

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. Stage2 49cbd00527..., release/1.0 @ b68c0c65708.

Repro (end-to-end): `test/fixtures/bootstrap/stage2_micro/micro_g/main.spl` —
`struct Pair<A, B>: a: A, b: B`; `val q = Pair<text, text>(a: "a", b: "b")`; `q.a + q.b`.
Symptom: `MIR lowering error: unresolved method call: operator overload for struct A (no matching
__add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl)` — worker exit 1 before codegen (~75 s).
The binop sees its operands typed `A` (the parameter name, resolved as a user struct), not `text`.

Relation to BUG-IT-3: same root — generic STRUCTS are templates the native path never instantiates:
a generic impl METHOD call dies at link (IT-3), a generic FIELD read with an operator dies in MIR
(IT-6). `[mono]` counts `generic_structs_found` but creates no struct specializations.

Ask: instantiate generic struct field types at the constructor's explicit type args before MIR
binop resolution, or fail closed with a diagnostic naming the field rather than "struct A".
