# Reverse-reference receipt ordering and publication

**Status:** AUTHORED / NOT_RUN. This manual describes nine executable scenarios in [the spec](../../../../../test/01_unit/compiler/cache/reverse_reference_sort_equivalence_spec.spl). It is not a runner result or a generated-document validation receipt.

The production receipt owner now sorts ordinary NUL-free inputs through the canonical ordering helper and reuses encoded bytes for the publication digest. These scenarios compare actual production output against a provider-relative insertion-order oracle. Fixed byte fixtures additionally protect historical read compatibility; they do not measure throughput or qualify a full compiler build.

## Compare provider ordering

1. Select empty text, ASCII prefixes, accented Latin, Greek, CJK and emoji values.
2. Compare every pair using the canonical text comparator and the active provider’s ordinary text comparison.
3. Require identical less-than results for every pair.

This is provider-specific execution evidence when run. One provider’s result cannot qualify all platforms.

## Preserve duplicates and multibyte receipt bytes

1. Construct ten unsorted projection rows, including duplicate `aa`, multibyte names and family marker strings.
2. Encode through the production receipt owner and independently through the historical-order oracle.
3. Require byte-for-byte identical output, an exact `sha256:` digest of those bytes, and ten retained projections.

## Compare provider-relative NUL ordering

1. Build `a NUL z` and `a NUL a` from explicit byte arrays using the production byte-to-text conversion.
2. Check the carrier length and bytes before testing the sort, preventing a truncated fixture from producing a false pass.
3. Include duplicate NUL-bearing rows and ordinary names; require the production encoded receipt to equal the historical-order bytes.

The control compares against the active provider, so it cannot prove pre-repair bytes are unchanged. Native length-aware ordering now distinguishes trailing bytes after NUL; fixed historical fixtures below make that difference explicit.

## Find NUL after multibyte characters

1. Construct two equal-prefix pairs from explicit UTF-8 bytes: three accented Latin characters or two emoji, then NUL and `z`/`a`.
2. Check the stored byte counts (8 and 10), NUL offsets (6 and 8), and suffix bytes before invoking the receipt owner. The NUL offsets exceed the respective code-point counts.
3. Put `z` before `a`, retain a duplicate and a NUL-free Unicode control, and require the encoded bytes and digest to match the independent legacy oracle.

These carriers exercise NUL beyond the code-point count. The provider-relative oracle follows the repaired full-length comparison; it is not a frozen strcmp oracle. Wire-length fields use the existing byte-count owner, independent of text `len()` semantics.

## Preserve terminal NUL

1. Build two accented characters followed by NUL using five explicit bytes.
2. Require the terminal byte at offset 4 to remain present.
3. Encode duplicate terminal-NUL rows with ordinary controls and compare against the legacy oracle.

## Preserve empty and invalid inputs

1. Encode an empty generation and compare its header/body with the historical oracle.
2. Try empty, newline-containing and carriage-return-containing consumer names.
3. Require both encoding and digest to return empty text for each invalid receipt.

## Publish the exact digest-addressed bytes

1. Create a process-specific temporary cache path and a real receipt containing duplicates and multibyte text.
2. Publish through the production generation owner.
3. Read `CURRENT` and require the exact tagged digest of the expected receipt.
4. Read the digest-addressed receipt, require the expected bytes, and verify the pointer/body match through the production helper.
5. Require successful removal of the temporary fixture directory.

Publication uses real filesystem operations. Missing pointer/body data fails assertions; it is not an accepted skip. The PID-based fixture assumes the coordinator serializes this spec and owns its temporary namespace; it is not a hostile same-user isolation test.

## Read fixed historical and repaired receipts

The independent `fixed_nul_receipt_v1` fixture contains explicit schema-1 key
frames and row lengths, all ten required projection families, and a 64-zero
syntactically valid projection digest. It calls neither production key encoding
nor sorting. The NUL byte uses the sanctioned explicit-length byte conversion;
its length and value are asserted before composing fixed rows.

1. A single `a NUL z` row with the other nine mandatory families forms a
   3,278-byte formerly admissible receipt. Require the fixed SHA256
   `b08620fba7dcf389b549c1c7406381efbb08aba7b83bb0292174d93fd24d4f96`,
   successful actual decoding, schema 1, ten rows, and byte-identical reencoding.
2. A fixed 3,584-byte old writer-only receipt puts `a NUL z` before `a NUL a`.
   Its fixed SHA256 is
   `e7258dbe207488b91d522b737355490137dc67426af54f755089e164f4cd5082`.
   Require actual rejection as `noncanonical-order-or-duplicate`.
3. The independently fixed full-byte order reverses those two rows and has
   SHA256 `4983c929aed5e3c1efa6efaa1c31743f2ffd6f64c9388a9fcc4ad2cd0a400dac`.
   Require actual decoding, eleven rows, byte-identical reencoding and matching
   tagged content digest. The source asserts old and repaired bytes differ.

The old core-C decoder already rejected distinct rows that strcmp considered
equal; the old tied encoding was not a qualified readable cache generation.
The fixed single-NUL case tests preservation of an admissible old receipt.
Schema and content-addressed storage stay unchanged; no blanket byte-equivalence
or automatic schema-version claim is made. Fixture lengths/digests were authored
independently from the declared wire layout; this is not execution evidence for
the Simple reader, encoder or runtime. Those assertions remain NOT_RUN.

## Execution and remaining qualification

An admitted source-matched full CLI must run this exact spec once under the campaign’s canonical process-tree watchdog, with retained logs, nonzero discovery, nine executed scenarios and no skipped requirement. The finite execution manifest assigns 120 seconds and a single native slot. Do not rerun an unchanged green result.

The separate cardinality spec and production performance probe cover other obligations. No runtime, branch-coverage, latency or RSS PASS is claimed here.

After runtime admission, validate this manual using the real `spipe-docgen` command for the spec with `--output doc/06_spec --no-index`; require complete documentation and `0 stubs`. Docgen is **NOT_RUN** and manual acceptance remains pending.
