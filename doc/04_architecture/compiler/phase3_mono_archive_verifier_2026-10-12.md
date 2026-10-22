# Complete archived post-mono verification

`mono_archive_verify_assembled_modules_v1` consumes complete assembled module
archives in the explicit representative order. It completes every closure-index
operation before starting any module walk. The retained `index_closure` now
delegates its unchanged per-module body to `PostMonoVerifier.index_module`; the
archived path calls that same method. Duplicate specialization diagnostics keep
their original position before all per-module diagnostics.

Index leases clone only mutable compact indexes into scratch, run the actual
index operation, and promote only changed SymbolId/name, template-name and
first-owner rows. Those rows are installed after scope close. Walker leases
borrow the two completed read-only closure indexes and invoke the existing
`verify_module` without changing its exhaustive variant handlers. Current
SymbolTable, current function ids, generic template ids, all expressions and
complete module bodies remain scratch. No verifier class is promoted.

Each lease starts a fresh report so only new violations escape. The owner merges
all 14 scalar counters and appends ordered text-only violations after close.
Symbol/chain context, specialization context and the existing transport receipt
counter are carried between leases, preserving the global 16-receipt limit.
No invariant, diagnostic or feature policy is disabled. The resulting report
still requires the driver's existing robust/critical policy, diagnostics,
statistics and pass-receipt publication. This function does not grant MIR
admission or convert an unverified descriptor into a final-stage descriptor.

The native fixture requires 80 checks. Added checks compare every report counter
and ordered rendered diagnostic against retained verification, refuse incomplete
or duplicate order, reject a forged final stage and refuse nested leases. A real
complete body with one cross-module duplicate specialization key is separately
published, decoded and verified; its positive E-MONO-037 counter and full report
must match the retained validator. Fixture allocation stays outside transient
scopes except the actual archive/validator operations and scalar/text captures.

Static validation checks the exact moved index body, unchanged exhaustive walker,
complete report counter merge and promotion exclusions. Native compilation and
execution are pending root serialization. No full driver activation, original
promoted-HIR reclamation or RSS improvement is established.

This depends on complete-module assembly `b71f0f483`, the shared original borrowed
reader `411f2c4`, and their selected-provider/publication schedule dependencies.
The remaining final repository boundary must bind actual execution coverage,
ordered body identities, this actual report, original-HIR semantic pass receipts,
and the driver's admitted diagnostic policy before MIR's final reader can open
the complete modules.
