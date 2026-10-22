# Structural union stage: representation and rollback

Requirement: C2 / REQ-C2-UNION-TRANSPORT-001. Status: thirteen authored production-API scenarios, **UNRUN**.

The scenarios lower actual source to HIR and invoke `source_union_normalize_v1`. They inspect semantic records instead of claiming success from a helper hash.

| Scenario | Observable result |
|---|---|
| Concrete bool introduction and member-dependent elimination | Exact enum owner, Bool/I64 canonical order, Tuple1 true payload, exact binder ID/type; actual MIR producer yields canonical discriminants and nonempty checked sites |
| Tagged identity through a local | Constructor count stays zero and original parameter ID remains the payload source |
| Retained default | Exactly one constructor retains the original bool operand; body remains a parameter reference |
| Optional member / nil | Constructor carries Unit and nil narrowing carries one wildcard slot |
| Resource boundaries | Actual successful usage is accepted at exact limit; one less refuses, input codec remains unchanged |
| Late failure | A later unsupported loop fails after earlier real injections, without caller HIR/registry mutation; next invocation succeeds independently |
| Supplied and omitted calls | Existing omitted argument list stays empty, supplied operand appears once inside the exact member constructor |
| Unnarrowed scalar conversion | No scalar cast can reinterpret a union tag; no module is returned |
| Ordinary enum source | Union-free HIR remains byte-identical |
| Known bool payload under integer result | Located refusal at the actual binder expression; complete caller HIR unchanged |
| Known integer guard / valid bool guard | Contradictory guard refuses at its span; correctly typed guard survives |
| Known direct-call formal mismatch / valid argument | Contradiction refuses without relabeling; valid argument keeps its original symbol |
| Admitted signature-only extern | Nil body remains absent; the separate actual union function still introduces its payload |

Default/call tests qualify only source normalization: downstream general-call export remains an explicit separate obligation. Input preservation uses the existing full HIR codec, including SymbolTable fields, alongside actual symbol/owner assertions. Logical counters do not prove physical dictionary-capacity work or measured RSS. No compiler, test runner, Lean kernel, native program or performance benchmark ran while authoring this packet.
