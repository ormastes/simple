# Target 6 native archive member streaming hash mismatch

Status: open. The candidate optimization was reverted after three bounded
build/fix cycles; the previously passing archive publisher remains in source.

`cold_hir_package_publication_v1.spl` currently copies each persisted archive
member into a byte array, validates it as UTF-8, and hashes the decoded text.
For a large package this retains a member-sized array and text alongside the
already resident archive. A candidate replaced the member copy with bounded
SHA-256 chunks and incremental UTF-8 validation, retaining only the manifest.

The candidate linked with `SIMPLE_NO_STUB_FALLBACK=1`, but the focused native
`cold_hir_compact_output_index_spec.spl` reported **4 examples, 2 failures**.
Both archive publication cases failed before moving `CURRENT`; the two graph
builder cases passed. The spec process exited 0 despite those failures, so its
exit code alone is not a PASS. One diagnostic run found member 0's streaming
digest `3af113f991b99b09a2a6deebe0c579fb86e3cd3f7166d4584bd59197234c31d2`
versus receipt digest
`9f63f2e1edaf9e26d3742a826204a1375848dc984c759e6016fa91d6aa7bd77c`.
Python SHA-256 of the fixture's `action|compile|function|foo|<compile digest>`
text agrees with the receipt. Allocating each chunk at its exact length rather
than slicing a fixed buffer still yielded 2 failures, so the slice is not a
sufficient explanation.

The available evidence does not isolate whether the discrepancy is in native
`Sha256StreamV1`, archive byte extraction, or their interaction. A next
session should compare the exact member bytes and a known nonempty SHA vector
inside one focused native probe before trying this optimization again. A
realistic paired time/RSS cohort is required before accepting any memory for
time tradeoff. No size, memory, or performance improvement is claimed here.

## Root isolated (2026-09-29 continuation)

A no-stub native probe fed the exact action-member text shown above through
three paths. `sha256_text` and `sha256_u8_hex` of the copied bytes both gave
the receipt digest `9f63…7bd77c`. `Sha256StreamV1.update` on that runtime-built
array gave the earlier bad `3af1…34c31d2`; direct `update_byte` calls gave
the receipt digest. The existing native stream spec passed four literal-array
vectors, so those vectors did not cover this runtime-built array shape.

`sha256_stream_v1_update` used unsigned indices for `[u8]` reads while the
working one-shot hasher used signed indices. Switching the stream's read loop
to signed indices and adding the exact runtime-built archive-member vector
made the no-stub native SHA spec pass 5/5, including both one-shot and
seven-byte chunk streams. The cold archive publisher still uses its previous
whole-member byte copy. Reapply bounded publication only after direct range
UTF-8 validation and a paired native time/RSS cohort; this bug remains open
until that production consumer is verified.
