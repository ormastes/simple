# Source monomorphization: bridge ownership and refusal

Requirements: REQ-FV2-C1-SM, ARCH-01, ARCH-02. Executable specification:
`test/01_unit/compiler/verify/source_calls_mono_bridge_v1_spec.spl`.

Status: **10 scenarios authored; all UNRUN**. Manually maintained companion;
qualified SPipe execution, generated-manual verification, compilation and
coverage remain pending. These assertions do not establish runtime qualification.

Fixtures use the real frontend and `HirLowering` to construct HIR, then invoke
`source_calls_monomorphize_v1`. The existing HIR encoder snapshots declarations,
default-expression graphs, symbol/scope rows and indexes for equality. Encoding
is a local mutation oracle; it does not admit the unavailable canonical codec.
Positive capture uses `lower_module_with_resolved_calls_for_target_v1` and the
actual completed-manifest validator under an explicit x86_64 Linux target.

| Scenario | Action | Required observation |
|---|---|---|
| Successful ownership and signatures | Specialize choose and its retained identity default | Two actual new declarations have symbol signatures matching ordered parameters/return; capture closes; complete input encoding/counters unchanged, even after mutating returned default annotations and a returned symbol index |
| Failure after one request | Discover two concrete requests in defaults with specialization cap one, then retry with a fresh normal pass | Precise specialization-limit refusal; complete input encoding unchanged; fresh invocation produces two specializations and closed capture |
| Unused retained template | Parse an uncalled generic declaration beside a concrete caller | `SOURCE-CALLS-E-G7`, without deleting the template or mutating input |
| Actual post-mono residual | Insert an unresolved type annotation in an actual completed specialization body | Real verifier reports a positive unresolved-type counter; bridge returns G7 refusal; mutated input remains unchanged |
| Exact work bound | Measure default-limit consumption, invoke fresh passes at that exact work and one less | Exact work succeeds with zero remaining and identical output identity; one less returns precise work refusal; input unchanged throughout |
| Bounded source entry | Invoke the public source API with two concrete requests and cap one/two | Cap one refuses; cap two yields two specializations and a closed two-binding manifest |
| Invalid limits | Pass zero and one over the maximum in each resource dimension | All six configurations return the real invalid-limit diagnostic and preserve input |
| Missing completed signature | Remove the signature from an actual specialized symbol row | Capture refuses with its signature diagnostic and preserves the supplied mutated module |
| Contradictory completed signatures | Independently reorder same-arity parameter types or change return type on actual specialized rows | Both capture attempts refuse without modifying their input modules |

| Absent declaration maps | Parse empty source, retain seven module dictionaries as nil, invoke actual HIR bridge | Fresh output dictionaries are empty, input dictionaries stay nil and complete input encoding is unchanged; this is the parsed-HIR bridge API rather than textual source entry |

No fabricated specialized declaration/body or fake verifier report is used.
Effect-order/payload mutations, other symbol-identity mutations, ambient-policy
checks and external command dispatch are separate obligations; these ten cases
do not claim to cover them. Formal status remains unchecked pending execution
and the broader verification/trust gates.
