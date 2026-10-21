# Native MIR workers repeat the full frontend before claiming work

Status: candidate fix in progress; runtime verification UNRUN. BugDB
registration pending a qualified CLI; no successful registration is claimed.

Observed on 2026-10-21: the live Phase 3 worker with producer SHA-256
`645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a`
used approximately one CPU during MIR lowering, with about 41 GiB RSS in the
captured process observation. Its matched source/build provenance remains
limited; the observation must not be represented as an independently admitted
compiler benchmark. The live process and its source/cache were not changed.

The release380 source independently demonstrates the mechanism: the ordinary
MIR lowering loop is serial; process MIR sharding is opt-in; every existing
MIR worker runs through full HIR/typecheck/mono before claiming its share.
The declaration-export writer hashes encoded post-mono HIR and discards it,
and its consumer validates summaries only after repeating the frontend.

The isolated candidate reuses the process ledger, declaration carrier, body
codec, transient ownership and object emission boundaries. It persists complete
post-mono bodies, admits immutable provider metadata, and claims physical
emission jobs before body loading. Each process owns one physical emission and
its logical specialization bodies. At most fifteen jobs run concurrently under
explicit phase admission. Parent order and context-bound object witnesses
govern final publication. No globally shared mutable lowering or new raw MIR
transport is introduced.

Required evidence before closing: real LLVM/Cranelift native semantic
comparisons at one/two/fifteen admitted workers, actual overlapping lowering
intervals, deterministic ordered inputs and contexts across job schedules,
cold/warm cache reuse, specialized physical aliases, stale/malformed artifact
refusal, failure isolation/reaping, and measured aggregate memory admission.
Current static/unit specifications are preparation for those gates, not PASS.
