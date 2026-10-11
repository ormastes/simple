# Prescan SymbolKind unit owner diagnostic workaround

Status: OPEN (P1)

Actual module_lowering.spl1323 Class | Struct pattern was newly observed during the eighteen-file diagnostic continuation. Qualify only the proven SymbolKind unit alternatives. Source commit a225e10cb retains the actual imported declared owner. Related receipt: phase3_prescan_symbolkind_workaround_2026-10-10.json. Full compilation and runtime qualification remain pending; no object or native PASS is asserted.
