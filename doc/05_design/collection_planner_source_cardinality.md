# Literal source cardinality

`collection_plan_source_facts(expr)` begins with unknown source facts. Only an
expression with `has_type_`, Array type, and HIR ArrayLit kind receives
`Exact(elements.len())`. Empty literals have zero slots. The count describes the
array if construction succeeds, not whether its evaluation completes or is pure.

The actual producer in
`hir_lowering/_Expressions/expression_core.spl` lowers AST ArrayLit through
`lower_expr_list`; `expression_components.spl` appends one lowered expression
for each item. HIR declares `ArrayLit([HirExpr], type?)` and a separate ArrayRepeat
variant, with no spread variant or expansion marker. Therefore the HIR literal
slot count is exact; this does not assert frontend spread support.

Variables, calls, repeated-array expressions, and fixed-length type annotations
do not provide this evidence. Existing canonical-loop source variables continue
to use unknown source facts. Effects, cost, allocation, order, uniqueness, alias,
purity, escape, equality, profitability, and evidence receipt are unchanged.
The helper neither evaluates elements nor authorizes a physical rewrite.

Tests cover literal counts through actual chain extraction plus exclusions and
an effectful element. Tests were authored before implementation; execution and
cross-engine evidence remain pending. No runtime or performance result is claimed.
