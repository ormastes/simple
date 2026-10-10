# Imported enum unit patterns omit the canonical field owner

Status: native first-loss reproduced; proposed repair UNVERIFIED.

Source 03e52e27a12bb9e4de41d47c09bcdf58fde7e790, trace-only source 4124380ad2e85181cb70eef4f3f6f86e62d18504, trace producer SHA 98a35379112503f0b291515023c9560ffab0642fd6186b959792248e14210b1b. Hello object/link/run PASS. Actual imported HirExpr parameter `expr.kind` followed by `HirExprKind.UnitLit | NilLit` fails HIR `[] vs [NilLit]` in the fixture body.

The trace records exact canonical/subject enum ID 1 versus local/retained enum ID 84. Both NilLit and UnitLit are known unit variants. Materialized enums, retained IDs and scalar owner mirror each have 24 entries. This fixture establishes an identity mismatch, not missing enumeration. The importer may retain a prior qualified symbol while a later local alias refers to a distinct symbol; registration previously used only local lookup. No claim is made that every Phase3/4 failure has this cause.

Proposed repair registers existing unit and generic declaration metadata at both identities only when imported owner metadata plus both symbols' Enum kind, declaration name and defining module prove the same declaration. It changes no symbol-table bindings, binding-name fallback or strict OR validation. Unknown owner metadata cannot grant canonical membership. Own declarations and mutable patterns retain their existing semantics.

Required verification: new producer Hello; real direct_record object/HIR acceptance and genuine payload x/y mismatch rejection; structural canonical_unit_pattern_owner_spec.spl through a supported runtime. All repair checks remain UNEXECUTED. No full Phase3 retry is part of this repair preparation.

Durable evidence and SHA manifest: /mnt/c/Temp/simple-real-hir-owner-trace-evidence-20261010/first-loss.json. The first trace invocation stopped at SCV admission; its separate NOT_EXECUTED receipt is preserved. Corrected invocation used normal cold inventory initialization and reached the observed HIR failure.
