# Canonical retained-default substitution

Executable source: `test/01_unit/compiler/mono/retained_default_substitution_v1_spec.spl`.

**12 authored scenarios; execution UNRUN.** This manually maintained companion groups related acceptance cases. Qualified SPipe generation, execution, coverage, native memory/performance and formal verification remain pending. Source review does not establish any of those results.

| Step | Action | Required observation |
|---|---|---|
| Normalize and specialize actual defaults | Canonicalize a generic function, specialize concrete types, and apply its retained template recipe. | Nested call type arguments and prior-parameter references are substituted; complete input digests stay unchanged. |
| Preserve ordinary policy | Compare omitted policy with explicit false and compare signature-only projection. | Ordinary bytes remain identical; signature projection stays body/default-free. |
| Keep malformed evidence visible | Provide a present default without a payload and an unresolved type. | Missing payload refuses; unresolved type remains for strict G7 rather than receiving an invented value. |
| Traverse nested lambda defaults | Use the existing expression traversal with enabled retained defaults. | Policy reaches the lambda parameter defaults and retains the shared ledger. |
| Enforce resource boundaries | Measure actual work, run exact and one-short work controls, and exhaust depth. | Exact work succeeds; failure returns nil with a defined error and balanced depth; fresh ledgers recover. |
| Preserve nil array compatibility | Invoke real canonicalization and specialization on nil versus empty params/type-parameter rows under omitted/false/true policies. | Output matches the defined empty-array representation, input remains unchanged, and low budget returns a resource error instead of dereferencing nil. |
