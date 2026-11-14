# Accessor source-producer checkpoint

Date: 2026-11-14
Status: source implementation under review; all new executable tests UNRUN.

The driver now invokes a cold source-plan producer before MIR scheduling when
an actual field-selector atom exists. Ordinary functions named `get`/`set`
inside execution selectors do not activate it (corrective commit
`30b7073dfaed2cd082d65ae5c1043b29e17e3480`). Public get/set validation remains
E1507: this checkpoint does not announce executable language support.

## Actual source path

1. The generated HIR visitor inventories original fields and distinguishes
   assignment targets from RHS reads. Repeated/empty spans and nested-lambda
   fields fail rather than inherit a false parent function identity.
2. Shared AOP tokenization and Boolean evaluation select named field advice.
   Atom projection is private to this adapter; there is no second weaver.
   Advice inventory is canonically ordered independently of streaming versus
   retained HIR, then existing priority/specificity ordering applies.
3. Real local declarations or an authenticated unique explicit import route
   supply field ownership and existing member-access verdicts. Imported layout
   rows remain identity-only. Aliases, importing IDs, declaring IDs and physical
   IDs remain distinct; ambiguous/glob routes fail explicitly.
4. Handler resolution inspects the actual owning HirFunction, validates the
   synchronous zero-parameter unit contract, uses existing callable linkage,
   and hashes real canonical function encoding. Effects identity is not a
   lifetime/purity certificate.
5. The existing body-free MIR class/layout owners produce physical metadata.
   A sorted coordinator reservation seeds the existing canonical type-ID maps
   before worker lowering. Workers reject conflicting prior identities and
   verify the final physical field names/types before helper publication.
6. The driver freezes helper IDs, source/HIR snapshots, layout mode and complete
   plan identities before workers consume original source sites. Target/profile
   agreement, original HIR errors and symbol collisions fail closed.

## Current bounded profile and open work

The initial provider requires explicit no-GC, admitted LLVM Linux target context,
ordinary reference classes, and primitive bool/integer sibling fields. Existing
layout reordering with mismatched declaration names is rejected pending the
separate class/struct/CUDA identity repair and qualification. This limitation
is staging, not a replacement for the full selected feature scope.

Known text length pseudo-properties are explicitly unmatched; real class fields
named `len` remain field joinpoints. Other non-nominal/unknown field receivers
currently reject the module profile. Nested-lambda fields are unsupported even
when a narrower selector might ultimately exclude them. The actual producer
has no resolved field-attribute feed, so `attr` remains unavailable; derived
export attributes require their boundary facts. RMW, value aggregates, managed
reference fields, generic instances, imported/glob route ambiguity and broader
platform/backend transports remain explicit obligations.

Object-cache/private-metadata serialization admission is not complete. No
source or runtime capability is enabled until those paths preserve/reject the
contract, actual generated optimized binaries pass the getter/setter oracle,
and required compiler/tooling gates pass.

## Authored evidence

New specifications cover shared selector negatives/comments, actual HIR field
inventory, imported aliases/privacy, real parsed handler lookup/body identity,
canonical two-worker type reservation, source inventory ordering and builtin
text length versus a class field named `len`. The earlier source checkpoint's
18-invariant transient gate remains its own static evidence. No native/parser/
backend execution pass is claimed for this producer, and no old green check
was repeated to manufacture evidence.
