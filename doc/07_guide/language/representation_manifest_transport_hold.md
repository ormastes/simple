# A5 typed metadata transport follow-up

Source candidate date: 2026-10-21. Qualification: UNRUN.

The existing flat-AST and generated HIR codec could otherwise drop the new
representation declaration collection. This candidate explicitly refuses
serialization when the collection contains authority-bearing facts and bumps
the codec versions. It updates the HIR codec schema generator's opaque-type
owner and matching refusal projection. It does not claim regeneration.

Concrete remaining work is a typed, bounded codec for declaration components,
exact source/attribute/owned spans, reviewer/capability arrays, and source
digest; generated-code regeneration under an admitted engine; cold/warm
roundtrip and independent stale/truncation negatives; and archive ownership
transport. Admissions must remain invocation/policy-specific and must not be
serialized as raw authority.

Cycle 2 separates observation from authority: ordinary unannotated unsafe
modules retain their existing body-cache eligibility. The actual HIR unsafe
nodes supply missing-review diagnostics after fresh lowering and cache decode.
ABI semantic projection remains available and never supplies an exemption.
Typed source-authored representation metadata still refuses body transport.
Measure ordinary and annotated sources with paired baseline/candidate wall time
and peak RSS before qualification; no timing or memory result has been measured
in this source-only session.
