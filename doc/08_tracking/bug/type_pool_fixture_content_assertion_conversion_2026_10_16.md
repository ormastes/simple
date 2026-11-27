# Native fixture extraction changed array assertion semantics

BUG-TYPE-POOL-FIXTURE-CONTENT-20261016. Database entry pending: no database tool
available. This is a test-authoring regression, not an established language bug.

The original pool regression used std.spec.to_equal on arrays. Extraction into
the native helper in 79f7409876e replaced that with direct typed-array `!=`.
Independent inventory-control COFF disassembly for producer 0CD6 shows that
expression lowers to raw pointer comparison. Separately allocated arrays with
equal contents can therefore fail the helper without any ownership failure.

std.spec ExpectHelper.value is any; its to_equal comparison routes through the
tag-aware runtime equality path. The runtime has array length/element equality.
The bounded language-guide review establishes array copy/value behavior but no
definitive direct typed-array equality guarantee. We therefore correct our
fixture conversion rather than inventing a compiler language-contract defect.

The repair checks actual returned lengths, then each expected scalar element,
for both union and named generic argument pools after both scopes. This retains
the original content assertion and guards indexing by exact length. Native
qualification remains NOT_RUN until the frozen standalone entry is built and
executed. No inventory retry or broader equality change is included.

## Gzip header prerequisite probe — 2026-10-20

The admitted pure-Simple producer645e62a8 exhibits the same fixture-authoring
hazard: direct typed-byte-array `!=` rejects an absent gzip header even though
native length/index diagnostics show exactly31,139,8,0,0,0,0,0,0,3. The corrected
wire oracle checks scalar bytes and the native probe passes absent, empty and
UTF-8 filename vectors. This does not establish a new direct-array equality
language contract. Exact compile/run/source receipts are recorded in
`doc/03_plan/evidence/seven_plans/items247_gzip_and_suffixed_patterns_2026-10-20.md`.
