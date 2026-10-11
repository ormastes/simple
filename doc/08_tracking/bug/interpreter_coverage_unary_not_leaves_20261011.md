# BUG-INTERPRETER-COVERAGE-UNARY-NOT-LEAVES-20261011

Status: implementation repaired; admitted-runtime qualification pending.
Owner: `src/compiler/10.frontend/core/interpreter/eval.spl`,
`eval_control_condition`.

The condition evaluator recursively handles and/or composition but previously
sent unary-not to generic expression evaluation. It then recorded the negation
wrapper instead of the evaluated operand. Negating a conjunction also hid its
evaluated leaf probes despite preserving the expression result.

The repair traverses the unary operand through the same condition evaluator,
returns immediately on `eval_had_error`, and negates the resulting truth. The
operand retains its original source span and truth in the real runtime coverage
collector. And/or short-circuit evaluation remains on its existing owner path.

The new executable regression uses real arena AST constructors and the canonical
`std.nogc_sync_mut.sffi.coverage` facade. It checks operand and wrapper IDs,
skipped right-hand operands, and error propagation without invented probes.
It requires `SIMPLE_COVERAGE=1`; disabled collection is a failing precondition,
not a skip or substitute receipt. There are no new raw runtime declarations.

Pinned Windows Stage1 producer15102d diagnostic evidence: initial2/2 failure;
owner repair2/2 pass; separately changed facade input2/2 pass; additional error
criterion1/1 pass in a focused fixture. Prior passing criteria were not replayed
for the additional error check. The final three-example file was not rerun as
one suite. The linked runtime SDN records original leaf truth:

```text
90001, 101, <entry>, 1, 5, 1, 0
90002, 301, <entry>, 2, 6, 0, 1
```

Baseline instead recorded wrapper IDs201 and601. Source/log/runtime hashes and
all terminal receipts are retained in `build/phase1-coverage-not-20261011/`.
Zero rebuilds. Working/staged environment guards and the source-only SFFI audit
are separate source evidence, not native/provider admission.

The four existing criteria in `coverage_unary_not_conditions_spec.spl` remain
OPEN and unchanged: bounded leaf counting, legacy evaluator composition,
vector ordinal composition, and bounded allocation-free traversal. This narrow
repair does not add absent historical helper owners just to satisfy fragments.
Those criteria were not replayed or marked closed.

Required admitted pure-Simple compiler/lib/MCP checks and core/MCP runtime smokes
remain pending because neither Windows release runtime is installed. The
coverage harness must activate its real collector for the regression. Production
PR remains draft; this diagnostic does not qualify native or JIT execution.
