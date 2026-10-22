# Source-model structural unions

Requirement: C2 / REQ-C2-UNION-TRANSPORT-001. Status: ten authored scenarios, **UNRUN**.

The real source-model entrypoint must parse source, normalize typed unions, capture actual enum semantics and export the resulting Lean artifact. A returned error fails every positive case; no refusal is counted as union support.

1. Introduce a bool into an annotated local and narrow it; the integer arm reads its own payload binder.
2. Introduce a typed integer parameter into a union return; require constructor application in emitted code.
3. Forward an already tagged union through a local, then narrow without adding another wrapper.
4. Keep a parsed union parameter default while exporting member-dependent narrowing.
5. Reorder and duplicate source members while retaining the existing canonical enum identity.
6. Preserve explicit x86_64 and aarch64 target comments through the same source route.
7. Introduce Optional-member nil, preserve its Tuple1 Unit constructor/pattern, and capture its canonical tag and all three MIR arms before successful public export.
8. Parse a genuinely nested parenthesized union, assert the nested HIR input, and capture/export the flattened two-variant canonical registry declaration.
9. Preserve a duplicate-only source union as a one-variant sum with a real constructor and original operand, including public export and exact MIR payload.
10. Introduce and eliminate a parsed same-module nominal member; assert actual HIR declaration/binder owner, canonical MIR struct payload schema and generated constructor application.

The companion normalization spec checks exact payload values, arity, source/registry IDs, canonical discriminants, actual MIR capture, omission state and unchanged input. These generated artifacts are NOT_CHECKED; compilation by Lean, native execution, performance/RSS, runtime/core/MCP gates and complete C2 remain unqualified. General calls, nested aggregate unions, recursive Vector and mutation are separate obligations.
