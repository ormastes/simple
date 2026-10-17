# Deferred optional tuple payload ownership

Issue: https://github.com/ormastes/simple/issues/3051

Status: narrow source workaround; actual compiler transport root cause remains
unproven. Native/SSpec execution is pending coordinated qualification.

C36 pure-Simple producer
`5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`
passed HIR95/95 for deferred.spl's source closure, then reported five
GenericTemplate constructor payload mismatches plus unresolved template.name.
The frozen a9b534 receipt is under C06
`build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/mono-deferred/error-groups.json`.
C37 source `c9cb8d6ac95ab64c95dc74c46772d2c60002271e` retains the same callers.

Each deserialize_*_def owner declares one Optional tuple `(Definition, i64)?`.
Four caller branches used two postfix unwraps; Class projected fields directly
from the optional. The section loader likewise unwrapped its optional template
pair twice. This source shape does not establish where native type metadata
was lost; old comments explicitly described it as a staged workaround.

The replacement uses one explicit presence branch and a binding typed to the
actual definition owner before GenericTemplate construction. The section loader
uses the same shape with GenericTemplate. Nil still returns nil/false, existing
deserializer errors remain untouched, and the exact consumed offset is retained.
No enum payload validation, binary format, source visibility, or decoder API is
relaxed. This is not a permanent generic compiler type-projection repair.

The authored regression exercises all five actual deserializers using fixed
empty-body records, distinct names, and independent expected lengths
24/19/23/57/14. It checks owner, name, generic parameters, nonzero start and exact
consumed offset, full section publication, truncated/unknown-kind refusal, and
the section loader's false result on a failing optional record. These cases are
unexecuted; lower-level decoder defects can still block them honestly.

Manual reproduction entry remains
`src/compiler/40.mono/monomorphize/deferred.spl` using the existing reviewed
manual source-object harness, exact admitted producer/source/SCV identities,
private phase-bound caches and `SIMPLE_NO_STUB_FALLBACK=1`. Record HIR, MIR and
object outcomes separately. Do not launch until the coordinated 20 GiB free
disk floor is met. No compile was launched for this source candidate.

Canonical tracking: `deferred_optional_tuple_owner_2026_10_11`, OPEN in `doc/08_tracking/bug/bug_db.sdn`. Reviewed source `36a8d5b30ea1d0f2bc86ac76767c7b9ff9a71040` maps to local integration `f5a908e82dfa5cad0dc39ff971403a4e05a8a5bf`; neither this mapping nor source review claims release landing or native success.

Removal condition: Repair optional tuple projection and constructor owner transport; original forms must pass actual deferred HIR/MIR/object plus all five decoder and section loader regressions before a separate retirement. Keep OPEN until a separately qualified permanent repair and retirement.
