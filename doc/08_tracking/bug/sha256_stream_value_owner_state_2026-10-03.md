# Streaming SHA-256 loses value-owner updates

Status: OPEN; source-level finding, native regression execution UNRUN.
Found while repairing retained-file ownership for item4. This is a separate
crypto API migration, not fixed by the retained-file patch.

`src/lib/common/crypto/sha256.spl:410` declares `Sha256StreamV1` as a value class
with scalar `block_len`, `total_bytes` and `finished` fields. Free functions
`sha256_stream_v1_update` (line 505), `sha256_stream_v1_update_byte` (line 542),
`sha256_stream_v1_zeroize` (line 550) and finalization/helper operations receive
the stream by value and mutate their copy. Sequential caller state therefore
cannot be inferred to advance, even if native buffer operations themselves work.

Concrete affected caller chain:

- `src/app/scv/db/evidence_hydrate.spl`: repeated stream updates followed by
  `db_evidence_stream_finish` while reading actual retained-file chunks.
- `src/lib/scv/db_evidence_stream.spl`: evidence stream start/finalization
  delegates to the streaming SHA functions.
- `src/app/scv/db/evidence_closure.spl:44`: closure domain, root and object frames
  repeatedly update a retained stream before closure digest finalization.
- `test/fixtures/scv/db_hydration_fixture.spl`: the 100 MiB fixture performs
  100 separate updates before finalizing its expected content digest.

Repair obligation: choose one explicit owner contract, preferably mutable
methods on a `var` stream, or return the updated owner on every operation and
every error. Migrate the compression/push/finalization helpers as well as public
callers; wrapping the old free function in a method would retain the defect.
Do not change one-shot SHA-256 semantics as part of an unrelated workaround.

Required regressions: external SHA vectors fed one byte, irregular chunks and
multiple full blocks; assert original owner counters between calls; compare
chunked/one-shot digests; finalize exactly once; reject updates after finalize;
preserve intended state after failed updates; verify wipe disables the original
owner. Then execute small and 100 MiB SCV hydration/inspection scenarios.

Until repaired and executed, SCV hashing/hydration and dependent Phase 4 gates
remain blocked. Existing one-shot SHA use in pack policy digests and Mach-O page
signing is a separate path and is not implicated by this specific finding.
