# Source monomorphization: retained defaults

Requirements: REQ-FV2-C1-SM, ARCH-02. Executable specification:
`test/01_unit/compiler/verify/source_calls_mono_defaults_v1_spec.spl`.

Status: **9 scenarios authored; all UNRUN**. Manually maintained companion;
qualified SPipe execution, generated-manual verification, compilation and
coverage remain pending. Source assertions do not establish runtime or proof acceptance.

The first seven source-stage scenarios call `source_calls_from_source_v1` with an explicit target,
validates the completed manifest, and compares every binding's signature/body hash
with its actual final MIR declaration. Literal and data-flow assertions inspect
actual emitted calls in the straight-line caller, without guessing mangled names.

| Scenario | Action | Required observation |
|---|---|---|
| Default-only generic request | Omit `consume`'s `identity<i64>(7)` default | Two bound calls; identity receives 7 and its result reaches consume |
| Generic default substitution | Instantiate `choose<T>(first:T, second:T=identity<T>(first))` for i64 | Two bound calls; both first arguments are 41 and identity's result occupies choose's second argument |
| Nested omission | Omit consume's middle call, whose own argument defaults to identity | Three bound calls with exact result flow through both consumers |
| Fully supplied arguments | Call the same generic choose with 41 and 73 | Exactly one call binding and those two actual arguments; no default call emitted |
| Caller shadowing | Declare caller local `first=99`, then invoke choose with 41 | Default identity receives 41 from the earlier declaration parameter |
| Failure between same-name defaults | Lower literal 23, refuse a foreign-call default, then lower literal 47 at the same source path | Fresh output contains 47; original output still contains 23 and retains its manifest hash |
| Active cycle | Mutually omit defaults in two declarations | Actual `DEFAULT-CYCLE` refusal; no successful inventory |
| Existing MIR maximum depth | Parse HIR and call the existing resolved-lowering API directly for 128 default frames | Closed manifest containing 128 bindings |
| Existing MIR excessive depth | Parse HIR and call the existing resolved-lowering API directly for 129 default frames | Actual `DEFAULT-DEPTH` refusal; no partial inventory |

Inventory status remains `formal_status=NOT_CHECKED`. These cases exercise actual
frontend, canonical specialization, G7, MIR default evaluation and finalization APIs.
The last two controls isolate the unchanged MIR default-frame bound; the new whole-stage work cap may refuse these large modules earlier, so these controls do not claim source-stage budget admission. They do not execute generated machine code or authenticate formal checking.
Input-HIR clone/scope ownership, mutation refusals, work limits and ambient policy
have separate specification owners; this file does not claim those checks.
