# Layout closure Function pattern owner (#3052)

Historical failure: source a9b5343d9dfbb9e6a38e074d7162092c58191b34,
C36 producer 5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235.
Actual layout_attrs entry HIR87 PASS, then MIR B5b multiple wildcard arms.
Evidence: manual-c34-failure-representatives-c36/layout-attrs under the shared
phase3-whole-20261011-c06 evidence root. The error is repeated in preserved logs;
it is one distinct diagnostic, not three separate matches.

Read-only auxiliary decoding of all 87 HIR caches with the historical generated
schema and complete stream consumption found exactly one match with multiple
default-like arms: hir_symbol_table_methods.spl, SymbolTable.is_function. Its
bare Function arm is HirPatternKind.Binding(Function), followed by Wildcard.
The spans are all zero. The diagnostic decoder and resulting JSON are retained
in layout-wildcard-triage; these locate the source but are not compiler proof.

The declared payload is SymbolKind.Function. Bare Function also names parser
and HIR type variants. Optional get_symbol payload ownership is insufficient
for MIR's unit-variant restoration, so the bare arm acts as a default binding.
The exact source is unchanged in frozen C37 c9cb8d6ac95ab64c95dc74c46772d2c60002271e.
No layout_attrs source edits are warranted.

The bounded workaround explicitly imports SymbolKind and qualifies this one
arm, preserving lookup, nil handling and false for every other symbol kind.
The actual symbol-table fixture includes Function symbols with/without type,
non-Function symbols with function types, a variable literally named Function,
negative/high absent IDs, and parser/HIR Function variants in the same closure.

Canonical key: layout_symbol_function_pattern_owner_2026_10_11; GitHub #3052
was registered before edits. Separate metadata owner registers its OPEN row.
Source review and actual layout MIR/native object plus fixture execution are
required before native success. Permanent repair must restore optional enum
ownership and pass the original bare-pattern form; qualification of this source
workaround alone does not close the compiler bug. No full build is launched.

Canonical tracking: `layout_symbol_function_pattern_owner_2026_10_11`, OPEN in `doc/08_tracking/bug/bug_db.sdn`. Reviewed source `5cb485c4d44c18cf96852ace63bfa091890707ef` maps to local integration `bb701125d1e043385a14b945210100fe345d8dc2`; neither this mapping nor source review claims release landing or native success.

Removal condition: Repair optional enum owner propagation; restore original bare Function arm only after actual layout HIR/MIR/object and mixed-kind/absent-ID original-form fixture controls pass. Keep OPEN until a separately qualified permanent repair and retirement.
