# Concrete optional-text nil subpatterns

Requirement: `REQ-NONGENERIC-NESTED-OPTIONAL-NIL`.
Executable: `test/01_unit/compiler/50.mir/nested_optional_text_nil_pattern_spec.spl`.
Evidence: **UNRUN — no qualified changed runtime supplied.** This is an authored
scenario manual, not generated execution evidence or a production PASS.

1. Match a concrete non-generic optional-text enum. Absence chooses the nil arm;
   nonempty and empty present text choose Some; a different outer tag chooses
   its own arm.
2. Parse and lower separate data/consumer modules through production frontend,
   HIR, and MIR owners. Confirm no diagnostics in the default legacy MIR lane,
   whose semantic-capture flag is explicitly false.
3. Inspect the emitted nil predicate: one already-extracted payload argument,
   an i64 input and Bool result, with distinct success/fallthrough blocks.
   Confirm the producer occurs once and the matcher adds no enum/tuple allocation.
4. Reject a nil subpattern in a nonoptional integer slot; integer 3 remains
   ordinary data. Reject nil in a nonoptional text slot too.
5. Reject a same-spelled Data variant owned by an unrelated enum and preserve
   constructor diagnostics for a wrong payload type.

Scope: concrete declared Optional slots only. Generic Result/Option inference,
opt-in semantic capture, text-provenance workaround removal, and the historical
private consumer loop are unqualified. The compound #2981 issue remains on HOLD.
