# Layout closure SymbolKind.Function owner (#3052)

The fixture exercises real SymbolTable.is_function with typed/untyped Function,
Method, Variable named Function, TypeAlias, and missing IDs. Parser TypeKind and
HIR HirTypeKind Function variants coexist and have independent arity assertions.
Success requires exit 0 and `layout-symbol-function-owner: pass`. Compilation
alone is not execution proof. Use a pinned admitted self-hosted producer with
SIMPLE_NO_STUB_FALLBACK=1. Native qualification remains pending.
