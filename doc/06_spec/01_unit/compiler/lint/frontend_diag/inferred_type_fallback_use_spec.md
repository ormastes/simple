# Inferred type fallback use diagnostics

Source: `test/01_unit/compiler/lint/frontend_diag/inferred_type_fallback_use_spec.spl`.
Authored mirror; docgen and semantic execution NOT_RUN.

The spec parses actual model/provider/facade/consumer sources, constructs frozen
module surfaces, lowers the consumer, and invokes canonical HIR diagnostics.
It checks retained nominal owner layouts and exact annotation provenance,
explicit Any return warnings, empty collection warnings, inferred bindings,
shadowing, registry levels, and unresolved-callee silence.

Omitted provider and facade returns reproduce an unavailable imported callable
signature through ordinary source lowering. Both assert one declaration warning
across receiver/index/field uses, including location and reason. They do not
claim that imported return inference is implemented.

Three phase-contract controls isolate retained metadata on that parsed omitted
return fixture. They assert the exact callee and binding symbol IDs, non-generic
foreign Function identity, nil signature, inferred provenance, and stored type
carriers before diagnostics:

| Control | Binding type | Initializer type | Expected findings |
|---|---|---|---|
| Binding only | Concrete i64 | Absent (presence false) | 0 |
| Initializer only | Error | Present concrete i64 | 0 |
| Both unresolved | Error | Present Error | 1, exact missing-signature reason |

Deleting either production suppression guard makes its corresponding isolated
control expect zero where the ordinary missing-signature warning is generated.
This is source-level mutation sensitivity reasoning, not an executed mutation
result. No synthetic diagnostic receipt is supplied.

## External CLI reproduction boundary

`simple check` currently dispatches to `simple_semantic_check_source`, which
constructs `HirLowering.with_filename` without frozen imported module surfaces.
That route cannot faithfully reproduce this exact imported Function signature
condition: unresolved callee identity is deliberately excluded by the rule.
An unqualified CLI invocation with a missing warning is therefore not a passing
regression. The full multi-module driver owns a diagnostic consumer, but a
bounded supported external entrypoint and admitted full CLI still require
qualification. External system reproduction remains OPEN / NOT_RUN.
