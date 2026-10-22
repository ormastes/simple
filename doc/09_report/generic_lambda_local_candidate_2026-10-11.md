# Generic lambda-local inference candidate

STATUS: UNQUALIFIED. Focused executable regressions are UNRUN.

H-LAMBDA-LET was present: the local-binding collector visited a Lambda only when
no skipped expression contained it. A lambda passed to a call or method could
contain `val local: i64 = 7; identity(local)`, but its annotated local never entered
the inference environment, leaving identity unresolved.

The collector now traverses expression operands, collection and construction
contents, transfer values, conditions, guards, iterators and context expressions.
It deliberately stops at nested lambdas. Lambda rewriting enters a distinct copy
of the enclosing environment, seeds its concrete parameters, collects its body,
rewrites it, then restores the environment, return context and enum-pattern hint.
This retains captured evidence while preventing sibling parameter/local leakage.
An untyped parameter stays unknown. Local collection retains statement order and
uses resolved module-unique SymbolIds, never variable spelling.

Seven focused HIR regressions in `hir_monomorphization_rewrite_spec.spl` cover call
and method arguments, nested lambdas under return/array wrappers, sibling typed
parameters and captured evidence, refusal of an untyped sibling, and typed block
locals in binary operands, and sparse numeric capture-key integrity. Existing
return-context regressions remain applicable. The private copy normalizes keys
through decimal text conversion because bootstrap dictionaries can expose text
keys, then uses explicit numeric-key and HirType value bindings.
Copying the enclosing environment costs O(number of current bindings) per lambda;
there is no mutable snapshot alias or shared cross-lambda environment table.

Scope remains bounded: H-IFVAL's optional-binding convention and H-BUILTIN's
unanswered builtin/trait method results are unchanged. No widened inference
default, parser-lambda syntax fix, or runtime lambda qualification is claimed.

Parent independent source review accepted traversal and scope isolation; its
numeric-key concern is addressed explicitly above. Staged whitespace and the
working/staged runtime-facade and numbered-artifact guards passed. Runtime
execution remains required and is not replaced by these source checks.
