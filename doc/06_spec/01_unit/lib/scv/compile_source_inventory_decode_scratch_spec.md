# Canonical inventory decoder scratch regression

Executable specification: `test/01_unit/lib/scv/compile_source_inventory_decode_scratch_spec.spl`.

The seven examples verify canonical empty/nonempty round trips, trailing-newline rejection, duplicate/descending identities, Unicode byte order, all five digest facets and invalid paths, malformed-row error precedence, and canonical/overflowing decimals.

The separate `test/fixtures/scv_inventory_memory/decode_allocation.spl` diagnostic measures registered live objects during a caller-owned transient scope. It verifies a 128-row decoded result, successful scope retirement, a nonzero observation and fewer than 2,304 live objects. Its pinned P1 default-run baseline fails with 2,454; the candidate passes with 2,191. The pure interpreter cannot observe this runtime counter and must not stand in for that diagnostic.

This verifies a smaller decoded scratch graph. It does not qualify coordinator RSS, native code generation, or Phase2. See `doc/08_tracking/bug/scv_decode_canonical_scratch_2026_10_29.sdn` for producer, evidence and outstanding lifetime work.
