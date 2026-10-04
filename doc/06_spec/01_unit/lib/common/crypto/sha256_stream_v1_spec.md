# SHA-256 stream partition compatibility

Source: `test/01_unit/lib/common/crypto/sha256_stream_v1_spec.spl`.
Manual intent, 2026-10-04. Native execution and generated docgen: **UNRUN**.

Existing scenarios cover runtime-built archive bytes, mixed-byte vectors,
external repeated-byte vectors, empty/partial partitions and full-block tails.
They now retain mutable stream owners throughout each partition sequence.

After admission run `<runtime> test <spec> --native` and
`<runtime> spipe-docgen <spec> --output doc/06_spec --no-index`, requiring zero
stubs. Expected constants and source review alone are not execution evidence.
