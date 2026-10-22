# Bare enum pattern becomes a binding in canonical compiler source

Status: OPEN; declaring-owner/pattern inference defect remains unproved.

Actual a713/8b producer, source460, 89-module MIR object closure fails B5b. Schema-guided full-consumption inspection of all89 cached HIR modules finds one default-arm collision among138 matches: SymbolTable.is_function in hir_symbol_table_methods.spl. Source matches sym.kind with bare Function then wildcard; cached HIR instead contains Binding then Wildcard. The cache owner SHA is ee548efbe063f875509ff76834a47066ff84c5b0eba812be2618abe654f97a1c. No SymbolId or undefined-raw error remains in this attempt.

Compatibility workaround qualifies the existing enum member as SymbolKind.Function. It preserves the two boolean results and does not disable duplicate-default, enum identity or publication checks. This is a documented source workaround, not a completed parser repair. Source-level short bare-member syntax must still be investigated.

Native canonical object verification is pending. Evidence: build/review/item5-b5b-cached-hir-owner-20261014.json and item5-producer8b-private-qualification-20261013/blockid-object-build. Full Phase3 compilation and produced-compiler Hello are still required before landing.
