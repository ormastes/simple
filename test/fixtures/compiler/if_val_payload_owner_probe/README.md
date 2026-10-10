# Optional binding provenance

UNEXECUTED. Expected native stdout: 7, 0, 2, 7, 2, 7, 1 (one value per line), exit 0.
Checks present/absent optional primitive paths, explicit .? without double evaluation, while-val reevaluation once per condition, and an ordinary optional declaration consumed by a later if-val. Structural SSpec pins the ordinary declaration's Optional type separately; runtime output alone cannot establish that type.
The actual HirSymbol? receiver regression remains the real declaration dependency hir_symbol_table_methods.spl lookup_exact_type, exercised by real_hir_owner_probe/object_record. Require its HIR acceptance and retained object body under a fresh producer; don't replace it with this primitive control.
