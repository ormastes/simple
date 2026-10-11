# SourceChange shared contracts — authored manual

Status: UNRUN; this manual is authored, not emitted by SPipe docgen.

Executable owner: `test/01_unit/lib/source_change/contracts_v1_spec.spl`.

REQ-003: preserve hints without treating shape as proof; check path and edit identities. REQ-007: reject unknown schema, zero sequence and malformed roots/payload digests. REQ-024: bound byte extents, cumulative replacement claims, edit cardinality, per-field identities and aggregate metadata, including a transaction ID equal to its path.

Five scenarios use real common-owner predicates. They do not test snapshot hashing/admission, codecs, durable publication, freshness or BuildRunner integration. The shared sixteen-case native diagnostic currently fails before any case passes on the retained Stage 2 producer; explicit return-type control fails too. Full runtime test execution and generated documentation remain pending qualified tooling.
