# Imported struct construction borrows another provider's bare layout

Status: cycle-6 correction authored; runtime qualification pending.

Admitted cycle-5 producer:
9ce404cd5e5383a62cdc06c1e0f84152a9b07e057f5bd34266fac116025c1cc8.
Source c3e5a0f453f. Phase 2 compiled 1401 modules, linked and passed admission.
The store closure then completed MIR for 197/197 modules with zero failures,
clearing the previous unresolved identity-operator diagnostics. Its remaining
compile was interrupted; no store runtime PASS is claimed.

The expanded native fixture compiled but exited 23: distinct records differing
only in prefix compared equal. Independent source review found that lower_call
qualified Class constructors but left Struct constructors bare. The shared
lower_struct_construct read that bare field-order row and registered it as the
result's provenance. A first provider's value/marker row therefore caused a
second provider's prefix/value/marker constructor to ignore prefix and emit
two aggregate operands. Exact-owner structural equality reads three fields;
LLVM aggregate allocation uses operand count. This creates an out-of-bounds
read risk; no instrumented memory-safety PASS is claimed.

The stronger regression checks prefix/value/marker directly before equality.
It compiled and exited 28 with the unchanged cycle-5 producer, proving the
construction/field-read defect independently of structural equality. Logs and
hash-bound receipts are retained under
build/native_probe/imported-inequality-cycle6-red-<producer>/.

The correction resolves the original consumer-owned Struct declaration to
its registered qualified layout at the start of lower_struct_construct.
Every metadata access, aggregate operand and result provenance uses that key.
A missing exact layout emits a fatal diagnostic and defined local, rather than
borrowing a bare row. Resolved Struct calls reach the shared constructor before
the legacy bare-name admission gate. Struct literals already use that owner
and the same constructor. Existing Class handling is unchanged.

Authored regressions cover all three direct field values, named and literal
construction with reordered fields, exact three-operand MIR construction in
declared order, reversed provider registration, same-named custom/structural
providers, parameter and array comparisons, scalar arithmetic and returned
record fields. Independent read-only review found no blocking defect. A dedicated
missing-metadata negative regression remains a review limitation; runtime and
whole-compiler qualification are pending.

Both owned full-CLI qualification and provisional Phase 3 diagnostic were
stopped after the counterexample. Their caches and logs remain intact. The
Phase 3 diagnostic never produced an admitted compiler; no Phase 3 PASS or
landing is established. This is cycle 6 of the user-authorized six total cycles.
