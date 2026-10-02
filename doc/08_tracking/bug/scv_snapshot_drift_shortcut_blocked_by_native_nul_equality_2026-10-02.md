# SCV snapshot drift hash shortcut blocked by native NUL equality

Status: optimization rejected; no product change. Native behavioral and
performance measurements are pending an admitted producer.

Reviewed source: `f8a04eee` on `fix/bootstrap-memory-retention-20261002`.
Investigation branch: `docs/snapshot-digest-perf-blocker-20261002`.

## Bounded finding

`src/lib/scv/compile_snapshot.spl` rereads the live source after publishing its
chunk and materializing the destination. It converts the reread text to UTF-8
bytes and hashes it to set `source_drifted`. A proposed shortcut was to compare
the reread text with the original text first, retaining the existing digest
calculation for unequal text. This would remove one conversion and SHA request
for unchanged files without removing any integrity reread.

That shortcut is unsafe across the supported native paths:

- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3292` routes statically
  string-shaped equality to `rt_text_eq_any` (symbol at line 3294).
- `src/runtime/runtime_native.c:4388` implements that helper. After normalizing
  the two operands, line 4404 returns `strcmp(a, b) == 0`.
- Consequently the equal-length byte sequences `61 00 62` and `61 00 63`
  compare equal on this path, although their complete UTF-8 byte digests differ.
  A guard could skip hashing a real edit after the embedded NUL.
- `rt_string_eq` in the same C source at line 4352 uses explicit lengths and
  `memcmp`, but ordinary text equality does not consistently select that helper.
  The pure-Simple `src/runtime/simple_core/core_string.spl` implementation of
  `rt_string_eq` also uses lengths and `memcmp`; that alone does not establish
  correctness of every native lowering/provider combination.

The counterexample follows directly from source and the C `strcmp` contract.
No new native executable was built or run; this is not a produced-binary test
result. No claim is made that this path caused the observed bootstrap RSS spike.

## Rejected wrapper substitution

`sha256_text(data)` in `src/lib/common/crypto/sha256.spl` already calls
`sha256_u8_fast_hex(text_to_utf8_bytes(data))`.
`scv_content_id_for_u8(bytes)` in `src/lib/scv/store.spl` wraps the same fast
digest with `sha256_`. Substituting the text wrapper in the snapshot digest
helper retains the byte conversion and does not establish an allocation saving.
The provider conversion issue is separately tracked in
`scv_sha256_text_provider_conversion_2026-09-29.md`.

## Acceptance before reconsidering the shortcut

1. Prove an existing sanctioned comparison boundary compares complete byte
   lengths on the actual native and interpreted paths, including embedded NUL.
   Alternatively repair the equality provider/lowering in a separately owned
   change; adding a local runtime extern to the snapshot module is not a fix.
2. Compare old and candidate drift/digest outcomes for empty, unchanged and
   changed ASCII, non-ASCII, CRLF, same-length middle-NUL edits, and large inputs.
   Preserve the changed-text digest check, including its collision semantics.
3. Measure the same original/candidate materializer with an admitted native
   producer. Report exact binary/source identity, wall time and peak memory;
   retain all source, chunk and destination validation reads.

No snapshot source, live selective candidate, process, cache, or another agent's
benchmark fixture was changed by this investigation. The existing digest path
remains the safe implementation. There is no measured performance improvement.
