# Three-payload compile refinement — incomplete draft

- Executable: `test/00_formal_verification/compiler/three_payload_compile_refinement_spec.spl`
- Evidence class: bounded source replay definition; not `SourceRefined`.

## Added open-obligation replay

`rr_nil_history_refused` seeds an explicit empty genesis manifest, then checks
that mutation with `nil` history is refused and mutation with the complete
empty manifest is accepted. The corresponding Lean roots distinguish absent
history from an explicit empty list and model durable outcome resolution after
CAS conflict, cancellation, or lost acknowledgment.

## Scenario inventory

- current-source binding and forged receipt refusal;
- cold-two and warm-three broker replay;
- external/corrupt/incomplete authority refusal;
- RR replacement, consumer mismatch, and nil-history refusal; and
- journal replay/conflict/torn-tail, GC epoch, and source-staleness cases.

Frozen visible flow: pin one coherent generation; apply one scoped semantic
mutation; recompute the authenticated affected closure; publish or refuse one
coherent generation; verify exact reuse and confined consumer IO. These replay
cases do not execute the full flow.

These additions remain authored and unadmitted. They neither activate a
production gate nor prove host durability, semantic completeness, ordinary
compiler IO confinement, or source refinement.

This is an incomplete hand-authored draft, not generated-manual qualification.
