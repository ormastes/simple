# Native list comprehension lowering contract

Base: `91131f979318db787cd046df38e53fc9dcb3f59b`. No AST/HIR wire-layout
change, grammar change, full CLI build, bootstrap, shared-cache write, or push.
This fixes silent native projection loss, not the separate Phase2 optional-Add
diagnostic. User-selected scope: implement existing list-comprehension semantics.

## Shared semantic contract

- Rust AST fields remain `expr`, `pattern`, `iterable`, `condition`.
- Pure AST/HIR retain ordered clauses and existing node fields:
  `HirExprKind.Comprehension(HirComprehensionKind.List, expr, clauses)`;
  clauses remain `HirCompClauseKind.For(symbol, iterable)` / `If(condition)`.
- Lower each iterable in its enclosing scope before binding the generator.
  Bind array/slice element types and bounded-range integer types; infer the
  projection independently and return `Array(projection_type)`.
- Bindings are local to the comprehension, shadow outer bindings without
  overwriting them, and restore on both success and diagnostics. Later clauses
  can use earlier bindings but not vice versa. Nested comprehensions are scoped.
- Evaluate an iterable exactly once per entry into its generator. Traverse in
  source order. Evaluate filters before the projection; rejected iterations
  must not evaluate projection effects. Append each accepted projection once.
- Build a fresh typed empty array; empty input and filter-all-false are valid.
  Preserve existing runtime boxing/tagging and array append conventions.
- Unsupported iterable/pattern/clause shapes must produce explicit diagnostics
  even in lenient mode, never nil, a fabricated element, or a success placeholder.
- Preserve syntax already supported by each parser: Rust's single generator
  plus optional filter and nested expressions; pure-Simple's ordered clauses.

## Ownership and names

Rust owner: `/root/bootstrap_native_sampler`. Pure owner: parent-assigned agent.
Merge owner: `/root`. Final reviewer: independent Astra (not an implementer).
Lower-model sidecars: N/A, semantics-sensitive compiler change.

Pure owned files only:

1. `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`
2. `src/compiler/30.types/type_infer/inference_expr.spl`
3. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
4. New sibling `src/compiler/50.mir/_MirLoweringExpr/comprehension.spl` and its
   required owner-local import/registration (report exact extra owner before edit).
5. `test/01_unit/compiler/mir/mcdc_comprehension_filter_lowering_spec.spl`.

New pure MIR helper: `lower_list_comprehension`; recursive clause helper:
`lower_list_comprehension_clauses`. Reuse array allocation/decode/box/push helpers
from `lower_array_map` rather than a map-then-filter transformation. Rust helper
is independently `lower_list_comprehension`, yielding existing Block/For/If HIR.

## Acceptance and evidence

Shared native fixture: `test/fixtures/native/list_comprehension_semantics.spl`.
Manifest fixture: `test/fixtures/native/version_manifest_optional.spl`, with a
strict nonempty rendered projection assertion and parse/render/parse validity.
General checks: type-changing text projection, filter/body evaluation order,
single iterable evaluation, name shadowing/restoration, nested comprehensions,
empty results, bounded ranges, and strict invalid-pattern/type/name diagnostics.
Pure ordered-generator tests additionally cover dependent generators and scope.
Tests use explicit failing exit codes/native output or real SSpec expectations;
unfinished cases fail with `assert(false)`/`fail(...)`, never `pass_todo` or
unconditional success. Preserve true red and green output, binary/source hashes,
timing, peak RSS, and quiescent watchdog receipts. At most three fix/verify cycles.
Stage-scoped compiler evidence is not a general SSpec, release, or Phase2 PASS.
