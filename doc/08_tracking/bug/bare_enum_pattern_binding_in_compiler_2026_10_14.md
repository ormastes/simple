# Bare enum pattern becomes a binding in canonical compiler source

Status: fix-implemented-verification-pending; declaring-owner/pattern inference defect remains unproved.

Actual a713/8b producer, source460, 89-module MIR object closure fails B5b. Schema-guided full-consumption inspection of all89 cached HIR modules finds one default-arm collision among138 matches: SymbolTable.is_function in hir_symbol_table_methods.spl. Source matches sym.kind with bare Function then wildcard; cached HIR instead contains Binding then Wildcard. The cache owner SHA is ee548efbe063f875509ff76834a47066ff84c5b0eba812be2618abe654f97a1c. No SymbolId or undefined-raw error remains in this attempt.

Compatibility workaround qualifies the existing enum member as SymbolKind.Function. It preserves the two boolean results and does not disable duplicate-default, enum identity or publication checks. This is a documented source workaround, not a completed parser repair. Source-level short bare-member syntax must still be investigated.

Native canonical object verification is pending. Evidence: build/review/item5-b5b-cached-hir-owner-20261014.json and item5-producer8b-private-qualification-20261013/blockid-object-build. Full Phase3 compilation and produced-compiler Hello are still required before landing.

**Revalidated 2026-11-02: still plausible because OPEN; declaring-owner/pattern inference defect remains unproved; no merged fix commit with a passing regression is cited in this doc.**

## Root cause and fix (2026-11-03, lane s3g2)

Cause: `declared_match_subject_type` (`src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl`) recovered a subject type only from an expression annotation or a plain variable symbol. For `match sym.kind:` (a `HirExprKind.Field` over an optional-unwrapped value) it returned nil, so `lower_match_pattern_with_union_v1` took the untyped-subject path, where a bare name shared by several enums (`Function` in SymbolKind and others) is "contested" and deliberately binds as a catch-all. Fix: for `Field(_, _, resolved)` use the resolved field symbol's declared type. The typed path then yields a real Enum pattern when the subject enum owns the name. The SymbolKind.Function source workaround in `hir_symbol_table_methods.spl` is kept.

Spec: `test/01_unit/compiler/common/bare_enum_pattern_field_subject_spec.spl` (interpreter-green; pins the compiler-source shape).

Stage3 verify: build a producer from this commit, compile `src/compiler/20.hir/hir_symbol_table_methods.spl` with the unqualified `case Function:` temporarily restored in `SymbolTable.is_function`, and confirm the cached HIR holds `Enum` not `Binding` for that arm (no `bare variant ... binds as a catch-all` warning). Then drop the workaround.
