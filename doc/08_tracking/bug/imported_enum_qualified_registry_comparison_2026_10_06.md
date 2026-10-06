# Imported enum qualified registry comparison

Status: candidate repair; native verification pending.

Actual producer 7404 rejected ProcessObservationPacketKindV4 nested-field comparisons in process_ops.spl lines 1096 and 1119 as struct operators. Both helper builds failed; no helper binary qualification is claimed.

The MIR local_enum_type_id implementation requires a bare enum_variant_index name before looking at enum_variant_index_q. Imported registration can key the bare table by an alias while its declaration symbol retains the imported original name. The qualified registry is authoritative for an owned enum; the bare precondition incorrectly rejects it. The candidate checks declaration kind and the appropriate qualified or ownerless registry independently. A same-named real struct remains rejected.

Unit coverage includes qualified imported aliases with no original bare key, absent qualified entries, and a real struct with a colliding registry name. Full unit-module execution is pending.

The process_ops candidate replaces 12 packet-kind equality/inequality operations with equivalent typed variant patterns. Ticket, digest, acknowledgement, stream, and retirement guards remain intact. This temporary workaround is bug-linked and must be retired after native comparison qualification. It is a separate composition option: typed patterns may encounter the independently reported enum-match lowering failure.

Seed15102 direct-import controls pass: four packet kinds, 20 checks covering positive/negative Frozen, Ack, CleanupFrozen and equality/inequality equivalence. This establishes limited seed semantics only. Alias-import equality and pattern controls both fail in this seed; they are retained as failing controls. A diagnostic shows the alias variant constructor differs from the returned enum value. Do not describe the alias controls as passing or claim native equivalence.

The helper diagnostics also contain `enum match: unsupported arm pattern`. Its concrete originating source pattern is not yet identified. This candidate does not fix or suppress that error. A composed-source native fixture run plus both helper builds is required before acceptance. Struct-without-operator negative control must remain rejected.

Evidence: ../test-builders-606-newp2-7404-retained40/artifact/{generator,main-verdict}/compiler-log/diagnostics.json; pattern-matrix-seed-result.json; seed-fixture-results.json; direct-owner-seed logs. Baseline 606f4752742051b858bb6800e461d367910c9533. No live source or producer was modified.
